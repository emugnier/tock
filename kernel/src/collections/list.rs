#![feature(const_refs_to_cell)]

use vstd::prelude::*;

verus! {

use vstd::prelude::*;
use vstd::cell::*;

pub struct ListLink<'a, T: 'a + ?Sized>(PCell<Option<&'a T>>);

impl<'a, T: ?Sized> ListLink<'a, T> {
    pub const fn empty() -> (ListLink<'a, T>, Tracked<PointsTo<Option<&'a T>>>) {
        let (cell, points_to) = PCell::<Option<&'a T>>::new(None);
        (ListLink(cell), points_to)
    }
}

pub trait ListNode<'a, T: ?Sized> {
    fn next(&'a self) -> &'a ListLink<'a, T>;
}

pub struct List<'a, T: 'a + ?Sized + ListNode<'a, T>> {
    head: ListLink<'a, T>,
    ghost_state: Tracked<GhostState<'a, T>>,
}

pub tracked struct GhostState<'a, T: 'a + ?Sized + ListNode<'a, T>> {
    ghost cells: Seq<&'a PCell<Option<&'a T>>>,
    tracked points_to_map: Map<nat, PointsTo<Option<&'a T>>>,
}

pub struct ListIterator<'a, T: 'a + ?Sized + ListNode<'a, T>> {
    pub l: &'a List<'a, T>,
    pub cur: Option<&'a T>,
    pub index: Ghost<nat>,
}

impl<'a, T: ?Sized + ListNode<'a, T>> ListIterator<'a, T> {
    pub fn new(l: &'a List<'a, T>) -> ListIterator<'a, T> {
        let tracked points_to = l.ghost_state.borrow().points_to_map.tracked_borrow(0);
        let cur = *l.head.0.borrow(Tracked(points_to));
        ListIterator { l, cur, index: Ghost(0) }
    }

    pub fn next(&mut self) -> Option<&'a T> {
        match self.cur {
            Some(res) => {
                proof {
                    self.index@ = self.index@ + 1;
                }

                let next = res.next();
                let tracked points_to = self.l.ghost_state.borrow().points_to_map.tracked_borrow(
                    self.index@,
                );
                self.cur = *next.0.borrow(Tracked(points_to));
                Some(res)
            },
            None => None,
        }
    }

    pub fn last(&mut self) -> Option<&'a T> {
        let mut last = None;
        loop {
            let cur = self.next();
            if cur.is_none() {
                break ;
            } else {
                last = cur;
            }
        }
        last
    }
}

impl<'a, T: ?Sized + ListNode<'a, T>> List<'a, T> {
    pub const fn new() -> List<'a, T> {
        let (list_link, Tracked(points_to)) = ListLink::<T>::empty();
        let cell = &list_link.0;
        let mut ghost_state = Tracked(
            GhostState { cells: Seq::empty(), points_to_map: Map::tracked_empty() },
        );

        proof {
            ghost_state.borrow_mut().cells = ghost_state@.cells.push(cell);
            ghost_state.borrow_mut().points_to_map.tracked_insert(0, points_to);
        }

        let list = List { head: list_link, ghost_state };

        list
    }

    pub fn head(&self) -> Option<&'a T> {
        let tracked points_to = self.ghost_state.borrow().points_to_map.tracked_borrow(0);
        *self.head.0.borrow(Tracked(points_to))
    }

    pub fn push_head(&mut self, node: &'a T, next_points_to: Tracked<PointsTo<Option<&'a T>>>) {
        let tracked mut head_points_to = self.ghost_state.borrow_mut().points_to_map.tracked_remove(
            0,
        );
        let old_head_value = *self.head.0.borrow(Tracked(&head_points_to));
        node.next().0.write(Tracked(next_points_to.borrow_mut()), old_head_value);
        self.head.0.write(Tracked(&mut head_points_to), Some(node));
        let cell = &node.next().0;

        proof {
            self.ghost_state.borrow_mut().cells = self.ghost_state@.cells.insert(1, cell);
            self.ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(
                Map::<nat, nat>::new(
                    |j: nat| 2 <= j && j <= old(self).ghost_state@.cells.len(),
                    |j: nat| (j - 1) as nat,
                ),
            );
            self.ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
            self.ghost_state.borrow_mut().points_to_map.tracked_insert(1, next_points_to.get());
        }
    }

    pub fn push_tail(&'a mut self, node: &'a T, next_points_to: Tracked<PointsTo<Option<&'a T>>>) {
        node.next().0.write(Tracked(next_points_to.borrow_mut()), None);
        let last = {
            let mut iter = self.iter();
            (&mut iter).last()
        };
        match last {
            Some(last) => {
                let tracked mut tail_points_to =
                    self.ghost_state.borrow_mut().points_to_map.tracked_remove(
                    (old(self).ghost_state@.cells.len() - 1) as nat,
                );
                last.next().0.write(Tracked(&mut tail_points_to), Some(node));

                proof {
                    //self.ghost_state.borrow_mut().cells = self.ghost_state@.cells.push(&node.next().0);
                    self.ghost_state.borrow_mut().points_to_map.tracked_insert(
                        (old(self).ghost_state@.cells.len() - 1) as nat,
                        tail_points_to,
                    );
                    self.ghost_state.borrow_mut().points_to_map.tracked_insert(
                        old(self).ghost_state@.cells.len(),
                        next_points_to.get(),
                    );
                }
            },
            None => self.push_head(node, next_points_to),
        }
    }

    pub fn pop_head(&mut self) -> Option<&'a T> {
        let tracked mut head_points_to = self.ghost_state.borrow_mut().points_to_map.tracked_remove(
            0,
        );
        let remove = *self.head.0.borrow(Tracked(&head_points_to));
        match remove {
            Some(node) => {
                {
                    let tracked next_points_to =
                        self.ghost_state.borrow().points_to_map.tracked_borrow(1);
                    self.head.0.write(
                        Tracked(&mut head_points_to),
                        *node.next().0.borrow(Tracked(next_points_to)),
                    );
                }

                proof {
                    //self.ghost_state.borrow_mut().cells = self.ghost_state@.cells.remove(1);
                    self.ghost_state.borrow_mut().points_to_map.tracked_remove(1);
                    self.ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(
                        Map::<nat, nat>::new(
                            |j: nat| 1 <= j && j < self.ghost_state@.cells.len(),
                            |j: nat| (j + 1) as nat,
                        ),
                    );
                    self.ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
                }
            },
            None => {
                self.head.0.write(Tracked(&mut head_points_to), None);

                proof {
                    self.ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
                }
            },
        }
        remove
    }

    pub fn iter(&'a self) -> ListIterator<'a, T> {
        ListIterator::<T>::new(self)
    }
}

fn main() {
}

} // verus!
