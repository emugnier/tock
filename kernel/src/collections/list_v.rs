#![feature(const_refs_to_cell)]

use vstd::prelude::*;

verus! {

use vstd::cell::*;

pub struct ListLinkV<'a, T: 'a + ?Sized>(pub PCell<Option<&'a T>>);

impl<'a, T: ?Sized> ListLinkV<'a, T> {
    pub const fn empty() -> (res: (ListLinkV<'a, T>, Tracked<PointsTo<Option<&'a T>>>))
        ensures
            res.0.0.id() == res.1@.id(),
            res.1@.is_init(),
            match res.1@.value() {
                Option::Some(_) => false,
                Option::None => true,
            },
    {
        let (cell, points_to) = PCell::<Option<&'a T>>::new(None);
        (ListLinkV(cell), points_to)
    }
}

pub trait ListNodeV<'a, T: ?Sized> {
    fn next(&'a self, next_points_to: Tracked<&PointsTo<Option<&'a T>>>) -> (res: &'a ListLinkV<
        'a,
        T,
    >)
        ensures
            res.0.id() == next_points_to@.id(),
    ;
}

pub struct ListV<'a, T: 'a + ?Sized + ListNodeV<'a, T>> {
    pub head: ListLinkV<'a, T>,
}

pub tracked struct GhostState<'a, T: 'a + ?Sized + ListNodeV<'a, T>> {
    pub ghost cells: Seq<&'a PCell<Option<&'a T>>>,
    pub tracked points_to_map: Map<nat, PointsTo<Option<&'a T>>>,
}

pub struct ListIteratorV<'a, T: 'a + ?Sized + ListNodeV<'a, T>> {
    pub cur: Option<&'a T>,
    pub index: Ghost<nat>,
}

pub closed spec fn well_formed_node<'a, T: 'a + ?Sized + ListNodeV<'a, T>>(
    ghost_state: &Tracked<GhostState<'a, T>>,
    i: nat,
) -> bool {
    &&& ghost_state@.points_to_map.dom().contains(i)
    &&& ghost_state@.points_to_map[i].is_init()
    &&& ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id()
}

impl<'a, T: ?Sized + ListNodeV<'a, T>> ListIteratorV<'a, T> {
    pub fn new(l: &'a ListV<'a, T>, ghost_state: &Tracked<GhostState<'a, T>>) -> (res:
        ListIteratorV<'a, T>)
        requires
            ghost_state@.cells.len() >= 1,
            forall|i: nat|
                0 <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                    == ghost_state@.cells[i as int].id(),
            forall|i: nat|
                0 <= i < (ghost_state@.cells.len() - 1) as nat
                    ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            ghost_state@.cells[0].id() == l.head.0.id(),
        ensures
            res.cur == ghost_state@.points_to_map[0].value(),
            res.index@ == 0,
    {
        proof {
            assert(ghost_state@.points_to_map.dom().contains(0));
        }
        let tracked points_to = ghost_state.borrow().points_to_map.tracked_borrow(0);
        let cur = *l.head.0.borrow(Tracked(points_to));
        ListIteratorV { cur, index: Ghost(0) }
    }

    pub fn next(&mut self, ghost_state: &Tracked<GhostState<'a, T>>) -> (res: Option<&'a T>)
        requires
            ghost_state@.cells.len() > old(self).index@,
            forall|i: nat|
                old(self).index@ <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                    == ghost_state@.cells[i as int].id(),
            forall|i: nat|
                old(self).index@ <= i < (ghost_state@.cells.len() - 1) as nat
                    ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            old(self).cur == ghost_state@.points_to_map[old(self).index@].value(),
        ensures
            ghost_state@.cells.len() > self.index@,
            forall|i: nat|
                self.index@ <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                    == ghost_state@.cells[i as int].id(),
            forall|i: nat|
                self.index@ <= i < (ghost_state@.cells.len() - 1) as nat
                    ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            res == ghost_state@.points_to_map[old(self).index@].value(),
            self.cur == ghost_state@.points_to_map[self.index@].value(),
            match res {
                Option::Some(_) => old(self).index@ + 1 < ghost_state@.cells.len() && self.index@
                    + 1 <= ghost_state@.cells.len() && self.index@ == old(self).index@ + 1,
                Option::None => old(self).index@ + 1 == ghost_state@.cells.len() && self.index@ + 1
                    == ghost_state@.cells.len() && self.index@ == old(self).index@,
            },
    {
        proof {
            assert(ghost_state@.points_to_map.dom().contains(self.index@));
            assert(ghost_state@.points_to_map[self.index@].is_init());
            assert(ghost_state@.points_to_map[self.index@].id()
                == ghost_state@.cells[self.index@ as int].id());
        }
        match self.cur {
            Some(res) => {
                proof {
                    assert(self.index@ < (ghost_state@.cells.len() - 1) as nat);
                    self.index@ = self.index@ + 1;
                    assert(ghost_state@.points_to_map.dom().contains(self.index@));
                    assert(ghost_state@.points_to_map[self.index@].is_init());
                    assert(ghost_state@.points_to_map[self.index@].id()
                        == ghost_state@.cells[self.index@ as int].id());
                }

                let tracked points_to = ghost_state.borrow().points_to_map.tracked_borrow(
                    self.index@,
                );
                let next = res.next(Tracked(points_to));
                self.cur = *next.0.borrow(Tracked(points_to));
                Some(res)
            },
            None => {
                proof {
                    assert(self.index@ + 1 == ghost_state@.cells.len());
                    assert(ghost_state@.points_to_map.dom().contains(self.index@));
                    assert(ghost_state@.points_to_map[self.index@].is_init());
                    assert(ghost_state@.points_to_map[self.index@].id()
                        == ghost_state@.cells[self.index@ as int].id());
                }

                None
            },
        }
    }

    pub fn last(&mut self, ghost_state: &Tracked<GhostState<'a, T>>) -> (res: Option<&'a T>)
        requires
            ghost_state@.cells.len() > old(self).index@,
            forall|i: nat|
                old(self).index@ <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                    == ghost_state@.cells[i as int].id(),
            forall|i: nat|
                old(self).index@ <= i < (ghost_state@.cells.len() - 1) as nat
                    ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            old(self).cur == ghost_state@.points_to_map[old(self).index@].value(),
        ensures
            ghost_state@.cells.len() == self.index@ + 1,
            self.cur == ghost_state@.points_to_map[self.index@].value(),
            match res {
                Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                    (self.index@ - 1) as nat,
                ) && res == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                Option::None => old(self).index@ + 1 == ghost_state@.cells.len(),
            },
    {
        let mut last = None;
        assert(old(self).index@ == self.index@);
        loop
            invariant_except_break
                ghost_state@.cells.len() > self.index@,
                forall|i: nat|
                    self.index@ <= i < ghost_state@.cells.len()
                        ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                        && ghost_state@.points_to_map[i].is_init()
                        && ghost_state@.points_to_map[i].id() == ghost_state@.cells[i as int].id(),
                forall|i: nat|
                    self.index@ <= i < (ghost_state@.cells.len() - 1) as nat
                        ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                        Option::Some(_) => true,
                        Option::None => false,
                    },
                match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
                    Option::Some(_) => false,
                    Option::None => true,
                },
                self.cur == ghost_state@.points_to_map[self.index@].value(),
                match last {
                    Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                        (self.index@ - 1) as nat,
                    ) && last == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                    Option::None => self.index@ == old(self).index@,
                },
            ensures
                ghost_state@.cells.len() == self.index@ + 1,
                self.cur == ghost_state@.points_to_map[self.index@].value(),
                match last {
                    Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                        (self.index@ - 1) as nat,
                    ) && last == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                    Option::None => old(self).index@ + 1 == ghost_state@.cells.len(),
                },
        {
            let cur = self.next(ghost_state);
            if cur.is_none() {
                proof {
                    assert(match last {
                        Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                            (self.index@ - 1) as nat,
                        ) && last == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                        Option::None => old(self).index@ + 1 == ghost_state@.cells.len(),
                    });
                }
                break ;
            } else {
                proof {
                    assert(match cur {
                        Option::Some(_) => ghost_state@.points_to_map.dom().contains(
                            (self.index@ - 1) as nat,
                        ) && cur == ghost_state@.points_to_map[(self.index@ - 1) as nat].value(),
                        Option::None => false,
                    });
                }
                last = cur;
            }
        }
        last
    }
}

impl<'a, T: ?Sized + ListNodeV<'a, T>> ListV<'a, T> {
    pub closed spec fn well_formed_list(&self, ghost_state: &Tracked<GhostState<'a, T>>) -> bool {
        &&& ghost_state@.cells.len() >= 1
        &&& forall|i: nat| 0 <= i < ghost_state@.cells.len() ==> well_formed_node(ghost_state, i)
        &&& forall|i: nat|
            0 <= i < (ghost_state@.cells.len() - 1) as nat
                ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                Option::Some(_) => true,
                Option::None => false,
            }
        &&& match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
            Option::Some(_) => false,
            Option::None => true,
        }
        &&& ghost_state@.cells[0].id() == self.head.0.id()
    }

    pub const fn new() -> (res: (ListV<'a, T>, Tracked<GhostState<'a, T>>))
        ensures
            res.1@.cells.len() == 1,
            well_formed_node(&res.1, 0),
            res.0.well_formed_list(&res.1),
    {
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

    pub fn head(&self, ghost_state: &Tracked<GhostState<'a, T>>) -> (res: Option<&'a T>)
        requires
            ghost_state@.cells.len() >= 1,
            ghost_state@.points_to_map.dom().contains(0),
            ghost_state@.cells[0].id() == self.head.0.id(),
            ghost_state@.points_to_map[0].is_init(),
            ghost_state@.points_to_map[0].id() == self.head.0.id(),
        ensures
            ghost_state@.points_to_map[0].value() == res,
    {
        let tracked points_to = ghost_state.borrow().points_to_map.tracked_borrow(0);
        *self.head.0.borrow(Tracked(points_to))
    }

    pub fn push_head(
        &self,
        node: &'a T,
        next_points_to: Tracked<PointsTo<Option<&'a T>>>,
        ghost_state: &mut Tracked<GhostState<'a, T>>,
    )
        requires
            old(ghost_state)@.cells.len() >= 1,
            forall|i: nat|
                0 <= i < old(ghost_state)@.cells.len() ==> #[trigger] old(
                    ghost_state,
                )@.points_to_map.dom().contains(i) && old(ghost_state)@.points_to_map[i].is_init()
                    && old(ghost_state)@.points_to_map[i].id() == old(
                    ghost_state,
                )@.cells[i as int].id(),
            forall|i: nat|
                0 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> match #[trigger] old(
                    ghost_state,
                )@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            match old(ghost_state)@.points_to_map[(old(ghost_state)@.cells.len()
                - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            old(ghost_state)@.cells[0].id() == self.head.0.id(),
            next_points_to@.is_init(),
        ensures
            old(ghost_state)@.cells.len() + 1 == ghost_state@.cells.len(),
            self.well_formed_list(ghost_state),
            ghost_state@.points_to_map[0].value().unwrap() == node,
            forall|i: nat|
                0 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> #[trigger] old(
                    ghost_state,
                )@.points_to_map[i].value().unwrap() == ghost_state@.points_to_map[i
                    + 1].value().unwrap(),
    {
        proof {
            assert(ghost_state@.points_to_map.dom().contains(0));
        }
        let tracked mut head_points_to = ghost_state.borrow_mut().points_to_map.tracked_remove(0);
        let old_head_value = *self.head.0.borrow(Tracked(&head_points_to));
        let tracked mut next_ptr = next_points_to.get();
        let next_node = node.next(Tracked(&next_ptr));
        next_node.0.write(Tracked(&mut next_ptr), old_head_value);
        self.head.0.write(Tracked(&mut head_points_to), Some(node));
        let cell = &next_node.0;

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
            assert forall|i: nat| 2 <= i < ghost_state@.cells.len() implies well_formed_node(
                ghost_state,
                i,
            ) by {
                assert(1 <= i - 1 < old(ghost_state)@.cells.len());
                assert(old(ghost_state)@.cells[i - 1] == ghost_state@.cells[i as int]);
                assert(old(ghost_state)@.points_to_map.dom().contains((i - 1) as nat)
                    == ghost_state@.points_to_map.dom().contains(i));
                assert(old(ghost_state)@.points_to_map[(i - 1) as nat]
                    == ghost_state@.points_to_map[i]);
            }
        }
    }

    pub fn push_tail(
        &'a self,
        node: &'a T,
        next_points_to: Tracked<PointsTo<Option<&'a T>>>,
        ghost_state: &mut Tracked<GhostState<'a, T>>,
    )
        requires
            old(ghost_state)@.cells.len() >= 1,
            forall|i: nat|
                0 <= i < old(ghost_state)@.cells.len() ==> #[trigger] old(
                    ghost_state,
                )@.points_to_map.dom().contains(i) && old(ghost_state)@.points_to_map[i].is_init()
                    && old(ghost_state)@.points_to_map[i].id() == old(
                    ghost_state,
                )@.cells[i as int].id(),
            forall|i: nat|
                0 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> match #[trigger] old(
                    ghost_state,
                )@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            match old(ghost_state)@.points_to_map[(old(ghost_state)@.cells.len()
                - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            old(ghost_state)@.cells[0].id() == self.head.0.id(),
            next_points_to@.is_init(),
        ensures
            old(ghost_state)@.cells.len() + 1 == ghost_state@.cells.len(),
            self.well_formed_list(ghost_state),
            ghost_state@.points_to_map[(ghost_state@.cells.len() - 2) as nat].value().unwrap()
                == node,
            forall|i: nat|
                0 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> #[trigger] old(
                    ghost_state,
                )@.points_to_map[i].value().unwrap()
                    == ghost_state@.points_to_map[i].value().unwrap(),
    {
        let tracked mut next_ptr = next_points_to.get();
        let next_node = node.next(Tracked(&next_ptr));
        next_node.0.write(Tracked(&mut next_ptr), None);
        proof {
            assert(ghost_state@.points_to_map.dom().contains(
                (ghost_state@.cells.len() - 1) as nat,
            ));
        }
        let last = {
            let mut iter = self.iter(ghost_state);
            iter.last(ghost_state)
        };
        match last {
            Some(last) => {
                let tracked mut tail_points_to =
                    ghost_state.borrow_mut().points_to_map.tracked_remove(
                    (ghost_state@.cells.len() - 1) as nat,
                );
                last.next(Tracked(&tail_points_to)).0.write(
                    Tracked(&mut tail_points_to),
                    Some(node),
                );
                let cell = &next_node.0;

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

    pub fn pop_head(&self, ghost_state: &mut Tracked<GhostState<'a, T>>) -> (res: Option<&'a T>)
        requires
            old(ghost_state)@.cells.len() >= 1,
            forall|i: nat|
                0 <= i < old(ghost_state)@.cells.len() ==> #[trigger] old(
                    ghost_state,
                )@.points_to_map.dom().contains(i) && old(ghost_state)@.points_to_map[i].is_init()
                    && old(ghost_state)@.points_to_map[i].id() == old(
                    ghost_state,
                )@.cells[i as int].id(),
            forall|i: nat|
                0 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> match #[trigger] old(
                    ghost_state,
                )@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            match old(ghost_state)@.points_to_map[(old(ghost_state)@.cells.len()
                - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            old(ghost_state)@.cells[0].id() == self.head.0.id(),
        ensures
            self.well_formed_list(ghost_state),
            if old(ghost_state)@.cells.len() == 1 {
                old(ghost_state)@.cells.len() == ghost_state@.cells.len()
            } else {
                old(ghost_state)@.cells.len() - 1 == ghost_state@.cells.len() && old(
                    ghost_state,
                )@.points_to_map[0].value() == res && forall|i: nat|
                    1 <= i < (old(ghost_state)@.cells.len() - 1) as nat ==> #[trigger] old(
                        ghost_state,
                    )@.points_to_map[i].value().unwrap() == ghost_state@.points_to_map[(i
                        - 1) as nat].value().unwrap()
            },
    {
        proof {
            assert(ghost_state@.points_to_map.dom().contains(0));
        }
        let tracked mut head_points_to = ghost_state.borrow_mut().points_to_map.tracked_remove(0);
        let remove = *self.head.0.borrow(Tracked(&head_points_to));
        match remove {
            Some(node) => {
                proof {
                    assert(ghost_state@.cells.len() > 1);
                    assert(ghost_state@.points_to_map.dom().contains(1));
                }

                {
                    let tracked next_points_to = ghost_state.borrow().points_to_map.tracked_borrow(
                        1,
                    );
                    self.head.0.write(
                        Tracked(&mut head_points_to),
                        *node.next(Tracked(next_points_to)).0.borrow(Tracked(next_points_to)),
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
                    assert forall|i: nat|
                        1 <= i < ghost_state@.cells.len() implies well_formed_node(
                        ghost_state,
                        i,
                    ) by {
                        assert(old(ghost_state)@.cells[(i + 1) as int]
                            == ghost_state@.cells[i as int]);
                        assert(old(ghost_state)@.points_to_map.dom().contains((i + 1) as nat)
                            == ghost_state@.points_to_map.dom().contains(i));
                        assert(old(ghost_state)@.points_to_map[(i + 1) as nat]
                            == ghost_state@.points_to_map[i]);
                    }
                }
            },
            None => {
                proof {
                    assert(ghost_state@.cells.len() == 1);
                }

                self.head.0.write(Tracked(&mut head_points_to), None);

                proof {
                    ghost_state.borrow_mut().points_to_map.tracked_insert(0, head_points_to);
                }
            },
        }
        remove
    }

    pub fn iter(&'a self, ghost_state: &Tracked<GhostState<'a, T>>) -> (res: ListIteratorV<'a, T>)
        requires
            ghost_state@.cells.len() >= 1,
            forall|i: nat|
                0 <= i < ghost_state@.cells.len()
                    ==> #[trigger] ghost_state@.points_to_map.dom().contains(i)
                    && ghost_state@.points_to_map[i].is_init() && ghost_state@.points_to_map[i].id()
                    == ghost_state@.cells[i as int].id(),
            forall|i: nat|
                0 <= i < (ghost_state@.cells.len() - 1) as nat
                    ==> match #[trigger] ghost_state@.points_to_map[i].value() {
                    Option::Some(_) => true,
                    Option::None => false,
                },
            match ghost_state@.points_to_map[(ghost_state@.cells.len() - 1) as nat].value() {
                Option::Some(_) => false,
                Option::None => true,
            },
            ghost_state@.cells[0].id() == self.head.0.id(),
        ensures
            res.cur == ghost_state@.points_to_map[0].value(),
            res.index@ == 0,
    {
        proof {
            assert(ghost_state@.points_to_map.dom().contains(0));
        }
        ListIteratorV::<T>::new(self, ghost_state)
    }
}

fn main() {
}

} // verus!
