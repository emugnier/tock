// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.
//! Virtualize the Alarm interface to enable multiple users of an underlying
//! alarm hardware peripheral.
use core::borrow::Borrow;
use core::borrow::BorrowMut;

use vstd::cell::*;
use vstd::prelude::*;

use kernel::hil::time::{Ticks, Time};
use kernel::utilities::cells::OptionalCell;
use kernel::ErrorCode;

use crate::alarm_v::AlarmDriver;
use crate::list_v::{ListIteratorV, ListLinkV, ListNodeV, ListV, GhostState};

verus! {

/// A trait that defines the behavior of an alarm.
pub trait Alarm<'a>: Time {
    fn set_alarm(&self, reference: Self::Ticks, dt: Self::Ticks);
    fn get_alarm(&self) -> Self::Ticks;
    fn disarm(&self, state: &mut Tracked<VirtualMuxAlarmState<'a, Self>>) -> Result<(), ErrorCode> where Self: core::marker::Sized;
    fn is_armed(&self, state: &Tracked<VirtualMuxAlarmState<'a, Self>>) -> bool where Self: core::marker::Sized;
    fn minimum_dt(&self) -> Self::Ticks;
}

#[derive(Copy, Clone)]
struct TickDtReference<T: Ticks> {
    /// Reference time point when this alarm was setup.
    reference: T,
    /// Duration of this alarm w.r.t. the reference time point. In other words, this alarm should
    /// fire at `reference + dt`.
    dt: T,
    /// True if this dt only represents a portion of the original dt that was requested. If true,
    /// then we need to wait for another max_tick/2 after an internal extended dt reference alarm
    /// fires. This ensures we can wait the full max_tick even if there is latency in the system.
    extended: bool,
}

// VERUS-TODO: Remove the Copy trait from T once this is fixed
// cannot move out of `self.reference` which is behind a shared reference
impl<T: Ticks + Copy + Clone> TickDtReference<T> {
    #[inline]
    fn reference_plus_dt(&self) -> T {
        self.reference.wrapping_add(self.dt)
    }

    fn get_reference(&self) -> T {
        self.reference
    }
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct ExAlarmDriver<'a, A: Alarm<'a>>(AlarmDriver<'a, A>);

// pub struct AlarmDriver<'a, A: Alarm<'a>>
/// An object to multiplex multiple "virtual" alarms over a single underlying alarm. A
/// `VirtualMuxAlarm` is a node in a linked list of alarms that share the same underlying alarm.
#[verifier::reject_recursive_types(A)]
pub struct VirtualMuxAlarm<'a, A: Alarm<'a>> {
    /// Underlying alarm which multiplexes all these virtual alarm.
    mux: &'a MuxAlarm<'a, A>,
    /// Reference and dt point when this alarm was setup.
    dt_reference: PCell<TickDtReference<A::Ticks>>,
    /// Whether this alarm is currently armed, i.e. whether it should fire when the time has
    /// elapsed.
    armed: PCell<bool>,
    /// Next alarm in the list.
    next: ListLinkV<'a, VirtualMuxAlarm<'a, A>>,
    /// Alarm client for this node in the list.
    client: OptionalCell<&'a AlarmDriver<'a, A>>,
}

#[verifier::external]
impl<'a, A: Alarm<'a>> ListNodeV<'a, VirtualMuxAlarm<'a, A>> for VirtualMuxAlarm<'a, A> {
    fn next(&'a self, next_points_to: Tracked<&PointsTo<Option<&'a VirtualMuxAlarm<'a, A>>>>) -> &'a ListLinkV<'a, VirtualMuxAlarm<'a, A>> {
        &self.next
    }
}

pub tracked struct VirtualMuxAlarmState<'a, A: Alarm<'a>> {
    phantom: core::marker::PhantomData<A>,
    pub tracked dt_reference_pt: PointsTo<TickDtReference<<VirtualMuxAlarm<'a, A> as kernel::hil::time::Time>::Ticks>>,
    pub tracked armed_pt: PointsTo<bool>,
}

// #[verifier::external_fn_specification]
// pub fn ExListIterator<'a, T: ?Sized + ListNode<'a, T>>(list: &List<'a, T>) -> kernel::collections::list::ListIterator<'a,T> {
//     list.iter()
// }
// pub fn iter(&self) -> ListIterator<'a, T> {
//     ListIterator {
//         cur: self.head.0.get(),
//     }
// }
//     fn from(value: T) -> Self;
// #[verifier::external_fn_specification]
// fn from_requires_ensures(value: u32) -> Ticks
//     {
//         Ticks(value)
//     }
// #[verifier ::external_fn_specification]
// fn from_requires_ensures(value: u32) -> Ticks
// {
//     time::Ticks32::from(value)
// }
// #[verifier::external_trait_specification]
// pub trait ExFrom<T>: Sized{
//     type ExternalTraitSpecificationFor: core::convert::From<T>;
//     // fn from(value: T) -> core::convert::From<T>::from;
// }
// #[verifier::external_fn_specification]
// pub fn ex_from_ticks(val: u32) -> (ticks: Ticks)
// {
//     Ticks::from(val)
// }
// #[verifier::external_fn_specification]
// pub fn ex_from_impl<A: Ticks>(value: u32) -> (r: time::Ticks32)
// {
//     Ticks32::from(value)
// }
// #[verifier::external_fn_specification]
// pub fn from_requires_ensures<T>(a: T) -> T
// {
//     core::convert::From::from(a)
// }
// impl ExFrom<u32> for time::Ticks24 {
//     type ExternalTraitSpecificationFor = Self;
//     #[verifier::external_fn_specification]
//     fn from(value: u32) -> Self {
//         time::Ticks24(value)
//     }
// }
// impl From<u32> for Ticks32 {
//     fn from(val: u32) -> Self {
//         Ticks32(val)
//     }
// }
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
// VERUS-TODO: Verify the OptionnalCell type
pub struct ExOptionalCell<T>(OptionalCell<T>);

#[verifier::external_fn_specification]
pub const fn ExOptionalCellempty<T>() -> OptionalCell<T> {
    OptionalCell::empty()
}

#[verifier::external_fn_specification]
pub fn ExOptionalCellMap<T: Copy, F, R>(optcell: &OptionalCell<T>, closure: F) -> Option<R> where
    F: FnOnce(T) -> R,
 {
    optcell.map(closure)
}

impl<'a, A: Alarm<'a>> VirtualMuxAlarm<'a, A> {
    pub closed spec fn valid_state(&self, state: &Tracked<VirtualMuxAlarmState<'a, VirtualMuxAlarm<'a, A>>>) -> bool {
        &&& self.dt_reference.id() == state@.dt_reference_pt.id()
        &&& self.armed.id() == state@.armed_pt.id()
        &&& state@.dt_reference_pt.is_init()
        &&& state@.armed_pt.is_init()
    }

    /// After calling new, always call setup()
    pub fn new(mux_alarm: &'a MuxAlarm<'a, A>) -> (res: (
        VirtualMuxAlarm<'a, A>,
        Tracked<VirtualMuxAlarmState<'a, A>>,
        Tracked<PointsTo<Option<&'a VirtualMuxAlarm<'a, A>>>>,
    ))
        ensures
            res.0.dt_reference.id() == res.1@.dt_reference_pt.id(),
            res.0.armed.id() == res.1@.armed_pt.id(),
            res.1@.dt_reference_pt.is_init(),
            res.1@.armed_pt.is_init(),
            res.1@.armed_pt.value() == false,
            res.0.next.0.id() == res.2@.id(),
            res.2@.is_init(),
    {
        // let zero = A::Ticks::from(0);
        let zero = A::Ticks::from_or_max(0);
        let (dt_reference, Tracked(dt_reference_pt)) = PCell::new(
            TickDtReference { reference: zero, dt: zero, extended: false },
        );
        let (armed, Tracked(armed_pt)) = PCell::new(false);
        let (next, tracked_next_pt) = ListLinkV::empty();
        let phantom = core::marker::PhantomData;
        (
            VirtualMuxAlarm {
                mux: mux_alarm,
                dt_reference,
                armed,
                next,
                client: OptionalCell::empty(),
            },
            Tracked(VirtualMuxAlarmState { phantom, dt_reference_pt, armed_pt }),
            tracked_next_pt,
        )
    }

    // VERUS-TODO: Check if this one should be marked at external
    #[verifier::external]
    fn set_alarm_client(&self, client: &'a AlarmDriver<'a, A>) {
        self.client.set(client);
    }

    /// Call this method immediately after new() to link this to the mux, otherwise alarms won't
    /// fire
    pub fn setup(&'a self, next_pt: Tracked<PointsTo<Option<&'a VirtualMuxAlarm<'a, A>>>>, mux_alarm_state: Tracked<&'a mut MuxAlarmState<'a, A>>) {
        self.mux.virtual_alarms.push_head(self, next_pt, &mut Tracked(mux_alarm_state.borrow_mut().virtual_alarms_state));
    }
}

impl<'a, A: Alarm<'a>> Time for VirtualMuxAlarm<'a, A> {
    // type Frequency = A::Frequency;
    fn get_freq() -> u32 {
        1000
    }

    type Ticks = A::Ticks;

    fn now(&self) -> Self::Ticks {
        self.mux.alarm.now()
    }
}

impl<'a, A: Alarm<'a>> Alarm<'a> for VirtualMuxAlarm<'a, A> {
    fn disarm(&self, state: &mut Tracked<VirtualMuxAlarmState<'a, VirtualMuxAlarm<'a, A>>>) -> Result<(), ErrorCode>
    ensures
    self.valid_state(&state),
    self.dt_reference.id() == state@.dt_reference_pt.id(),
    {
        if !self.armed.get() {
            return Ok(());
        }
        self.armed.set(false);

        // let enabled = self.mux.enabled.get() - 1;
        // VERUS-TODO: Fix the above overflow in the above line and replace it
        let enabled = self.mux.enabled.get();
        self.mux.enabled.set(enabled);

        // If there are not more enabled alarms, disable the underlying alarm
        // completely.
        if enabled == 0 {
            let _ = self.mux.alarm.disarm();
        }
        Ok(())
    }

    fn is_armed(&self, state: &Tracked<VirtualMuxAlarmState<'a, VirtualMuxAlarm<'a, A>>>) -> (res: bool)
    ensures
    self.valid_state(state),
    state@.armed_pt.value() == res,
    {
        let tracked state = state.borrow();
        *self.armed.borrow(Tracked(&state.armed_pt))
    }

    fn set_alarm(&self, reference: Self::Ticks, dt: Self::Ticks) {
        let enabled = self.mux.enabled.get();
        let half_max = Self::Ticks::half_max_value();
        // If the dt is more than half of the available time resolution, then we need to break
        // up the alarm into two internal alarms. This ensures that our internal comparisons of
        // now outside of range [ref, ref + dt) will trigger correctly even with latency in the
        // system
        // VERUS-TODO define less than and greater than for Ticks?
        // Reason, arithmetic operations are not supported on the Ticks type
        let dt_reference = if dt.into_usize() > half_max.wrapping_add(
            self.minimum_dt(),
        ).into_usize() {
            TickDtReference { reference, dt: dt.wrapping_sub(half_max), extended: true }
        } else {
            TickDtReference { reference, dt, extended: false }
        };
        self.dt_reference.set(dt_reference);
        // Ensure local variable has correct value when used below
        let dt = dt_reference.dt;

        if !self.armed.get() {
            // VERUS-TODO prove that this line is not overflowing and uncomment
            // self.mux.enabled.set(enabled + 1);
            self.armed.set(true);
        }
        // First alarm, so set it

        if enabled == 0 {
            //debug!("virtual_alarm: first alarm: set it.");
            self.mux.set_alarm(reference, dt);
        } else if !self.mux.firing.get() {
            // If firing is true, the mux will scan all the alarms after
            // firing and pick the soonest one so do not need to modify the
            // mux. Otherwise, this is an alarm
            // started in a separate code path (e.g., another event).
            // This new alarm fires sooner if two things are both true:
            //    1. The current earliest alarm expiration doesn't fall
            //    in the range of [reference, reference+dt): this means
            //    it is either in the past (before reference) or the future
            //    (reference + dt), AND
            //    2. now falls in the [reference, reference+dt)
            //    window of the current earliest alarm. This means the
            //    current earliest alarm hasn't fired yet (it is in the future).
            // -pal
            let cur_alarm = self.mux.alarm.get_alarm();
            let now = self.mux.alarm.now();
            let expiration = reference.wrapping_add(dt);
            if !cur_alarm.within_range(reference, expiration) {
                // VERUS-TODO: Check if it is equivalent to the previous impl
                let next = self.mux.next_tick_vals.get();
                if let Some((next_reference, next_dt)) = next {
                    if now.within_range(next_reference, next_reference.wrapping_add(next_dt)) {
                        self.mux.set_alarm(reference, dt);
                    }
                } else {
                    self.mux.set_alarm(reference, dt);
                }
                // if next.map(|next| {
                //     let (next_reference, next_dt) = next;
                //     now.within_range(next_reference, next_reference.wrapping_add(next_dt))
                // })
                // .unwrap_or(true)
                // {
                //     self.mux.set_alarm(reference, dt);
                // }
            } else {
                // current alarm will fire earlier, keep it
            }
        }
    }

    fn get_alarm(&self) -> Self::Ticks {
        let dt_reference = self.dt_reference.get();
        let extension = if dt_reference.extended {
            Self::Ticks::half_max_value()
        } else {
            Self::Ticks::from_or_max(0)
        };
        dt_reference.reference_plus_dt().wrapping_add(extension)
    }

    fn minimum_dt(&self) -> Self::Ticks {
        self.mux.alarm.minimum_dt()
    }
}

impl<'a, A: Alarm<'a>> AlarmClient<'a, A> for VirtualMuxAlarm<'a, A> {
    // VERUS-TODO: Verify the AlarmDriver so that we don't have to trust this
    #[verifier::external_body]
    fn alarm(&self, state: &Tracked<MuxAlarmState<'a, A>>) {
        self.client.map(|client| client.alarm(state));
        // if  self.client.is_some() {
        //     let client = self.client.get().map(|client| client.alarm());
        // client.alarm();
        // }
    }
}

/// Structure to control a set of virtual alarms multiplexed together on top of a single alarm.
#[verifier::reject_recursive_types(A)]
pub struct MuxAlarm<'a, A: Alarm<'a>> {
    /// Head of the linked list of virtual alarms multiplexed together.
    virtual_alarms: ListV<'a, VirtualMuxAlarm<'a, A>>,
    /// Number of virtual alarms that are currently enabled.
    enabled: PCell<usize>,
    /// Underlying alarm, over which the virtual alarms are multiplexed.
    alarm: &'a A,
    /// Whether we are firing; used to delay restarted alarms
    firing: PCell<bool>,
    /// Reference to next alarm
    next_tick_vals: PCell<Option<(A::Ticks, A::Ticks)>>,
}

pub tracked struct MuxAlarmState<'a, A: Alarm<'a>> {
    pub tracked virtual_alarms_state: GhostState<'a, VirtualMuxAlarm<'a, A>>,
    pub tracked enabled_pt: PointsTo<usize>,
    pub tracked firing_pt: PointsTo<bool>,
    pub tracked next_tick_vals_pt: PointsTo<Option<(A::Ticks, A::Ticks)>>,
}

impl<'a, A: Alarm<'a>> MuxAlarm<'a, A> {
    pub const fn new(alarm: &'a A) -> (res: (MuxAlarm<'a, A>, Tracked<MuxAlarmState<'a, A>>))
    ensures
    res.0.enabled.id() == res.1@.enabled_pt.id(),
    res.0.firing.id() == res.1@.firing_pt.id(),
    res.0.next_tick_vals.id() == res.1@.next_tick_vals_pt.id(),
    res.1@.enabled_pt.is_init(),
    res.1@.firing_pt.is_init(),
    res.1@.next_tick_vals_pt.is_init(),
    res.1@.enabled_pt.value() == 0,
    res.1@.firing_pt.value() == false,
    res.1@.next_tick_vals_pt.value().is_none(),
    {
        let (virtual_alarms, Tracked(virtual_alarms_state)) = ListV::new();
        let (enabled, Tracked(enabled_pt)) = PCell::new(0);
        let (firing, Tracked(firing_pt)) = PCell::new(false);
        let (next_tick_vals, Tracked(next_tick_vals_pt)) = PCell::new(None);
        (MuxAlarm {
            virtual_alarms,
            enabled,
            alarm,
            firing,
            next_tick_vals,
        }, Tracked(MuxAlarmState {
            virtual_alarms_state,
            enabled_pt,
            firing_pt,
            next_tick_vals_pt,
        }))
    }

    pub fn set_alarm(&self, reference: A::Ticks, dt: A::Ticks) {
        self.next_tick_vals.set(Some((reference, dt)));
        self.alarm.set_alarm(reference, dt);
    }

    pub fn disarm(&self) {
        self.next_tick_vals.set(None);
        let _ = self.alarm.disarm();
    }
}

pub trait AlarmClient<'a, A: Alarm<'a>> {
    fn alarm(&self, state: &Tracked<MuxAlarmState<'a, A>>);
}

impl<'a, A: Alarm<'a>> AlarmClient<'a, A> for MuxAlarm<'a, A> {
    /// When the underlying alarm has fired, we have to multiplex this event back to the virtual
    /// alarms that should now fire.
    fn alarm(&self, state: &Tracked<MuxAlarmState<'a, A>>) {
        let tracked state = state.borrow();
        // Check whether to fire each alarm. At this level, alarms are one-shot,
        // so a repeating client will set it again in the alarm() callback.
        self.firing.set(true);
        let mut iterator = ListIteratorV::new(&self.virtual_alarms, &Tracked(state.virtual_alarms_state));
        // for cur in self.virtual_alarms.iter() {
        // while let Some(cur) = current {
        loop {
            match iterator.next(&Tracked(state.virtual_alarms_state)) {
                Some(cur) => {
                    let dt_ref = cur.dt_reference.get();
                    let now = self.alarm.now();
                    if cur.armed.get() && !now.within_range(
                        dt_ref.reference,
                        dt_ref.reference_plus_dt(),
                    ) {
                        if dt_ref.extended {
                            cur.dt_reference.set(
                                TickDtReference {
                                    reference: dt_ref.reference_plus_dt(),
                                    dt: A::Ticks::half_max_value(),
                                    extended: false,
                                },
                            );
                        } else {
                            cur.armed.set(false);
                            // VERUS-TODO uncomment the following line and prove the lack of overflow
                            // self.enabled.set(self.enabled.get() - 1);
                            cur.alarm();
                        }
                    }
                },
                None => break ,
            }
            // let mut current = self.virtual_alarms.head();

        }
        self.firing.set(false);
        // Find the soonest alarm client (if any) and set the "next" underlying
        // alarm based on it.  This needs to happen after firing all expired
        // alarms since those may have reset new alarms.
        let now = self.alarm.now();
        // let next = self
        //     .virtual_alarms
        //     .iter()
        //     .filter(|cur| cur.armed.get())
        //     .min_by_key(|cur| {
        //         let when = cur.dt_reference.get();
        //         // If the alarm has already expired, then it should be
        //         // considered as the earliest possible (0 ticks), so it
        //         // will trigger as soon as possible. This can happen
        //         // if the alarm expired *after* it was examined in the
        //         // above loop.
        //         if !now.within_range(when.reference, when.reference_plus_dt()) {
        //             A::Ticks::from(0u32)
        //         } else {
        //             when.reference_plus_dt().wrapping_sub(now)
        //         }
        //     })
        let mut iterator = ListIteratorV::new(&self.virtual_alarms, &Tracked(state.virtual_alarms_state));
        let mut min_ticks = None;
        let mut min_alarm = None;

        loop {
            match iterator.next(&Tracked(state.virtual_alarms_state)) {
                Some(cur) => {
                    if cur.armed.get() {
                        let when = cur.dt_reference.get();
                        let ticks = if !now.within_range(when.reference, when.reference_plus_dt()) {
                            A::Ticks::from_or_max(0u64)
                        } else {
                            when.reference_plus_dt().wrapping_sub(now)
                        };

                        match min_ticks {
                            None => {
                                min_ticks = Some(ticks);
                                min_alarm = Some(cur);
                            },
                            Some(min) if ticks.into_usize() < min.into_usize() => {
                                min_ticks = Some(ticks);
                                min_alarm = Some(cur);
                            },
                            _ => {},
                        }
                    }
                },
                None => break ,
            }
        }

        let next = min_alarm;

        // Set the alarm.
        if let Some(valrm) = next {
            let dt_reference = valrm.dt_reference.get();
            self.set_alarm(dt_reference.reference, dt_reference.dt);
        } else {
            self.disarm();
        }
    }
}

} // verus!
