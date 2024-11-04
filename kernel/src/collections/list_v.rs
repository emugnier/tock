#![feature(const_refs_to_cell)]

use vstd::prelude::*;

verus! {

use vstd::cell::*;

pub struct ListLinkV<'a, T: 'a + ?Sized>(PCell<Option<&'a T>>);

impl<'a, T: ?Sized> ListLinkV<'a, T> {
    pub const fn empty() -> (ListLinkV<'a, T>, Tracked<PointsTo<Option<&'a T>>>) {
        let (cell, points_to) = PCell::<Option<&'a T>>::new(None);
        (ListLinkV(cell), points_to)
    }
}

pub trait ListNodeV<'a, T: ?Sized> {
    fn next(&'a self) -> &'a ListLinkV<'a, T>;
}

pub struct ListV<'a, T: 'a + ?Sized + ListNodeV<'a, T>> {
    head: ListLinkV<'a, T>,
}

pub tracked struct GhostState<'a, T: 'a + ?Sized + ListNodeV<'a, T>> {
    ghost cells: Seq<&'a PCell<Option<&'a T>>>,
    tracked points_to_map: Map<nat, PointsTo<Option<&'a T>>>,
}

pub struct ListIteratorV<'a, T: 'a + ?Sized + ListNodeV<'a, T>> {
    pub cur: Option<&'a T>,
    pub index: Ghost<nat>,
}

impl<'a, T: ?Sized + ListNodeV<'a, T>> ListIteratorV<'a, T> {
    pub fn new(l: &'a ListV<'a, T>, ghost_state: &Tracked<GhostState<'a, T>>) -> ListIteratorV<
        'a,
        T,
    > {
        let tracked points_to = ghost_state.borrow().points_to_map.tracked_borrow(0);
        let cur = *l.head.0.borrow(Tracked(points_to));
        ListIteratorV { cur, index: Ghost(0) }
    }

    pub fn next(&mut self, ghost_state: &Tracked<GhostState<'a, T>>) -> Option<&'a T> {
        match self.cur {
            Some(res) => {
                proof {
                    self.index@ = self.index@ + 1;
                }

                let next = res.next();
                let tracked points_to = ghost_state.borrow().points_to_map.tracked_borrow(
                    self.index@,
                );
                self.cur = *next.0.borrow(Tracked(points_to));
                Some(res)
            },
            None => None,
        }
    }

    pub fn last(&mut self, ghost_state: &Tracked<GhostState<'a, T>>) -> Option<&'a T> {
        let mut last = None;
        loop {
            let cur = self.next(ghost_state);
            if cur.is_none() {
                break ;
            } else {
                last = cur;
            }
        }
        last
    }
}

impl<'a, T: ?Sized + ListNodeV<'a, T>> ListV<'a, T> {
    pub const fn new() -> (ListV<'a, T>, Tracked<GhostState<'a, T>>) {
        let (list_link, Tracked(points_to)) = ListLinkV::<T>::empty();
        let cell = &list_link.0;
        let mut ghost_state = Tracked(
            GhostState { cells: Seq::empty(), points_to_map: Map::tracked_empty() },
        );

        proof {
            ghost_state.borrow_mut().cells = ghost_state@.cells.push(cell);
            ghost_state.borrow_mut().points_to_map.tracked_insert(0, points_to);
        }

        let list = ListV { head: list_link };

        (list, ghost_state)
    }

    pub fn head(&self, ghost_state: &Tracked<GhostState<'a, T>>) -> Option<&'a T> {
        let tracked points_to = ghost_state.borrow().points_to_map.tracked_borrow(0);
        *self.head.0.borrow(Tracked(points_to))
    }

    pub fn push_head(
        &self,
        node: &'a T,
        next_points_to: Tracked<PointsTo<Option<&'a T>>>,
        ghost_state: &mut Tracked<GhostState<'a, T>>,
    ) {
        let tracked mut head_points_to = ghost_state.borrow_mut().points_to_map.tracked_remove(0);
        let old_head_value = *self.head.0.borrow(Tracked(&head_points_to));
        let tracked mut next_ptr = next_points_to.get();
        node.next().0.write(Tracked(&mut next_ptr), old_head_value);
        self.head.0.write(Tracked(&mut head_points_to), Some(node));
        let cell = &node.next().0;

        proof {
            ghost_state.borrow_mut().cells = ghost_state@.cells.insert(1, cell);
            ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(
                Map::<nat, nat>::new(
                    |j: nat| 2 <= j && j < ghost_state@.cells.len(),
                    |j: nat| (j - 1) as nat,
                ),
            );
            ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
            ghost_state.borrow_mut().points_to_map.tracked_insert(1, next_ptr);
        }
    }

    pub fn push_tail(
        &'a self,
        node: &'a T,
        next_points_to: Tracked<PointsTo<Option<&'a T>>>,
        ghost_state: &mut Tracked<GhostState<'a, T>>,
    ) {
        let tracked mut next_ptr = next_points_to.get();
        node.next().0.write(Tracked(&mut next_ptr), None);
        let last = {
            let mut iter = self.iter(ghost_state);
            (&mut iter).last(ghost_state)
        };
        match last {
            Some(last) => {
                let tracked mut tail_points_to =
                    ghost_state.borrow_mut().points_to_map.tracked_remove(
                    (ghost_state@.cells.len() - 1) as nat,
                );
                last.next().0.write(Tracked(&mut tail_points_to), Some(node));
                let cell = &node.next().0;

                proof {
                    ghost_state.borrow_mut().cells = ghost_state@.cells.push(cell);
                    ghost_state.borrow_mut().points_to_map.tracked_insert(
                        (ghost_state@.cells.len() - 2) as nat,
                        tail_points_to,
                    );
                    ghost_state.borrow_mut().points_to_map.tracked_insert(
                        (ghost_state@.cells.len() - 1) as nat,
                        next_ptr,
                    );
                }
            },
            None => self.push_head(node, Tracked(next_ptr), ghost_state),
        }
    }

    pub fn pop_head(&self, ghost_state: &mut Tracked<GhostState<'a, T>>) -> Option<&'a T> {
        let tracked mut head_points_to = ghost_state.borrow_mut().points_to_map.tracked_remove(0);
        let remove = *self.head.0.borrow(Tracked(&head_points_to));
        match remove {
            Some(node) => {
                {
                    let tracked next_points_to = ghost_state.borrow().points_to_map.tracked_borrow(
                        1,
                    );
                    self.head.0.write(
                        Tracked(&mut head_points_to),
                        *node.next().0.borrow(Tracked(next_points_to)),
                    );
                }

                proof {
                    ghost_state.borrow_mut().cells = ghost_state@.cells.remove(1);
                    ghost_state.borrow_mut().points_to_map.tracked_remove(1);
                    ghost_state.borrow_mut().points_to_map.tracked_map_keys_in_place(
                        Map::<nat, nat>::new(
                            |j: nat| 1 <= j && j < ghost_state@.cells.len(),
                            |j: nat| (j + 1) as nat,
                        ),
                    );
                    ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
                }
            },
            None => {
                self.head.0.write(Tracked(&mut head_points_to), None);

                proof {
                    ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
                }
            },
        }
        remove
    }

    pub fn iter(&'a self, ghost_state: &Tracked<GhostState<'a, T>>) -> ListIteratorV<'a, T> {
        ListIteratorV::<T>::new(self, ghost_state)
    }
}

fn main() {
}

} // verus!
