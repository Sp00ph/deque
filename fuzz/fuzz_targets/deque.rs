#![no_main]
use std::{collections::VecDeque, mem};

use arbitrary::Arbitrary;
use deque::Deque;
use libfuzzer_sys::fuzz_target;

#[derive(Arbitrary, Debug)]
enum Op {
    Append,
    Back,
    Clear,
    Contains(i32),
    Drain(usize, usize, Vec<DrainOp>),
    Equals,
    Front,
    Get(usize),
    Insert(usize, i32),
    IsEmpty,
    Iter,
    Len,
    MakeContiguous,
    PopBack,
    PopFront,
    PushBack(i32),
    PushFront(i32),
    Range(usize, usize),
    Remove(usize),
    Retain(i32),
    RotateLeft(usize),
    RotateRight(usize),
    ShrinkToFit,
    SplitOff(usize),
    Swap(usize, usize),
    SwapRemoveBack(usize),
    SwapRemoveFront(usize),
    Truncate(usize),
}

const MAX_LEN: usize = 1000000;

#[derive(Arbitrary, Debug)]
enum DrainOp {
    Next,
    NextBack,
    Drop,
}

fuzz_target!(|data: Vec<Op>| { fuzz(&data) });

fn fuzz(data: &[Op]) {
    let (mut d1, mut d2) = (Deque::<i32>::new(), Deque::<i32>::new());
    let (mut v1, mut v2) = (VecDeque::<i32>::new(), VecDeque::<i32>::new());

    for op in data {
        match op {
            Op::Append => {
                d1.append(&mut d2);
                v1.append(&mut v2);
                // dbg!("append", &d1, &v1, &d2, &v2);
            }
            Op::Back => {
                // dbg!("back", &d1, &v1, &d2, &v2);
                assert_eq!(d1.back(), v1.back());
                assert_eq!(d2.back(), v2.back());
            }
            Op::Clear => {
                d1.clear();
                d2.clear();
                v1.clear();
                v2.clear();
            }
            Op::Contains(i) => {
                assert_eq!(d1.contains(i), v1.contains(i));
                assert_eq!(d2.contains(i), v2.contains(i));
            }
            Op::Drain(min, max, ops) => {
                if v1.is_empty() || v2.is_empty() {
                    continue;
                }
                let mut min1 = min % v1.len();
                let mut min2 = min % v2.len();
                let mut max1 = max % v1.len();
                let mut max2 = max % v2.len();
                if min1 > max1 {
                    mem::swap(&mut min1, &mut max1)
                }
                if min2 > max2 {
                    mem::swap(&mut min2, &mut max2)
                }

                let mut d1_drain = d1.drain(min1..max1);
                let mut d2_drain = d2.drain(min2..max2);
                let mut v1_drain = v1.drain(min1..max1);
                let mut v2_drain = v2.drain(min2..max2);

                for op in ops {
                    match op {
                        DrainOp::Next => {
                            assert_eq!(d1_drain.next(), v1_drain.next());
                            assert_eq!(d2_drain.next(), v2_drain.next());
                        }
                        DrainOp::NextBack => {
                            assert_eq!(d1_drain.next_back(), v1_drain.next_back());
                            assert_eq!(d2_drain.next_back(), v2_drain.next_back());
                        }
                        DrainOp::Drop => {
                            drop(d1_drain);
                            drop(d2_drain);
                            drop(v1_drain);
                            drop(v2_drain);
                            assert!(d1.iter().eq(v1.iter()));
                            assert!(d2.iter().eq(v2.iter()));
                            break;
                        }
                    }
                }
            }
            Op::Equals => {
                assert!(d1.iter().eq(v1.iter()));
                assert!(d2.iter().eq(v2.iter()));
            }
            Op::Front => {
                assert_eq!(d1.front(), v1.front());
                assert_eq!(d2.front(), v2.front());
            }
            Op::Get(i) => {
                assert_eq!(d1.get(*i), v1.get(*i));
                assert_eq!(d2.get(*i), v2.get(*i));
                let i1 = *i & v1.len();
                let i2 = *i & v2.len();
                assert_eq!(d1.get(i1), v1.get(i1));
                assert_eq!(d2.get(i2), v2.get(i2));
            }
            &Op::Insert(i, a) => {
                if !v1.is_empty() {
                    let i1 = i % v1.len();
                    d1.insert(i1, a);
                    v1.insert(i1, a);
                }

                if !v2.is_empty() {
                    let i2 = i % v2.len();
                    d2.insert(i2, a);
                    v2.insert(i2, a);
                }
                // dbg!("insert", &d1, &v1, &d2, &v2);
            }
            Op::IsEmpty => {
                assert_eq!(d1.is_empty(), v1.is_empty());
                assert_eq!(d2.is_empty(), v2.is_empty());
            }
            Op::Iter => {
                let mut d1_iter = d1.iter();
                let mut v1_iter = v1.iter();
                while v1_iter.len() > 0 {
                    if fastrand::bool() {
                        assert_eq!(d1_iter.next(), v1_iter.next());
                    } else {
                        assert_eq!(d1_iter.next_back(), v1_iter.next_back());
                    }
                }

                let mut d2_iter = d2.iter();
                let mut v2_iter = v2.iter();
                while v2_iter.len() > 0 {
                    if fastrand::bool() {
                        assert_eq!(d2_iter.next(), v2_iter.next());
                    } else {
                        assert_eq!(d2_iter.next_back(), v2_iter.next_back());
                    }
                }
            }
            Op::Len => {
                assert_eq!(d1.len(), v1.len());
                assert_eq!(d2.len(), v2.len());
            }
            Op::MakeContiguous => {
                assert_eq!(d1.make_contiguous(), v1.make_contiguous());
                assert_eq!(d2.make_contiguous(), v2.make_contiguous());
            }
            Op::PopBack => {
                assert_eq!(d1.pop_back(), v1.pop_back());
                assert_eq!(d2.pop_back(), v2.pop_back());
            }
            Op::PopFront => {
                assert_eq!(d1.pop_front(), v1.pop_front());
                assert_eq!(d2.pop_front(), v2.pop_front());
            }
            Op::PushBack(i) => {
                if v1.len() < MAX_LEN {
                    d1.push_back(*i);
                    v1.push_back(*i);
                }
                if v2.len() < MAX_LEN {
                    d2.push_back(*i);
                    v2.push_back(*i);
                }
            }
            Op::PushFront(i) => {
                if v1.len() < MAX_LEN {
                    d1.push_front(*i);
                    v1.push_front(*i);
                }
                if v2.len() < MAX_LEN {
                    d2.push_front(*i);
                    v2.push_front(*i);
                }
                // dbg!("push_front", &d1, &v1, &d2, &v2);
            }
            &Op::Range(min, max) => {
                if !v1.is_empty() {
                    let mut min1 = min % v1.len();
                    let mut max1 = max % v1.len();
                    if min1 > max1 {
                        mem::swap(&mut min1, &mut max1)
                    }

                    assert!(d1.range(min1..max1).eq(v1.range(min1..max1)));
                }

                if !v2.is_empty() {
                    let mut min2 = min % v2.len();
                    let mut max2 = max % v2.len();
                    if min2 > max2 {
                        mem::swap(&mut min2, &mut max2)
                    }
                    assert!(d2.range(min2..max2).eq(v2.range(min2..max2)));
                }
            }
            &Op::Remove(i) => {
                if !v1.is_empty() {
                    let i1 = i % v1.len();
                    // dbg!(i1);
                    assert_eq!(d1.remove(i1), v1.remove(i1));
                }
                if !v2.is_empty() {
                    let i2 = i % v2.len();
                    assert_eq!(d2.remove(i2), v2.remove(i2));
                }
                // dbg!("remove", &d1, &v1, &d2, &v2);
            }
            Op::Retain(max) => {
                let f = |j: &i32| j <= max;
                d1.retain(f);
                d2.retain(f);
                v1.retain(f);
                v2.retain(f);
            }
            Op::RotateLeft(i) => {
                if !v1.is_empty() {
                    let i1 = i % v1.len();
                    d1.rotate_left(i1);
                    v1.rotate_left(i1);
                }
                if !v2.is_empty() {
                    let i2 = i % v2.len();
                    d2.rotate_left(i2);
                    v2.rotate_left(i2);
                }
            }
            Op::RotateRight(i) => {
                if !v1.is_empty() {
                    let i1 = i % v1.len();
                    d1.rotate_right(i1);
                    v1.rotate_right(i1);
                }
                if !v2.is_empty() {
                    let i2 = i % v2.len();
                    d2.rotate_right(i2);
                    v2.rotate_right(i2);
                }
            }
            Op::ShrinkToFit => {
                d1.shrink_to_fit();
                d2.shrink_to_fit();
                v1.shrink_to_fit();
                v2.shrink_to_fit();
            }
            Op::SplitOff(i) => {
                if !v1.is_empty() {
                    let i = i % v1.len();
                    d2 = d1.split_off(i);
                    v2 = v1.split_off(i);
                }
            }
            Op::Swap(i, j) => {
                if !v1.is_empty() {
                    let i1 = i % v1.len();
                    let j1 = j % v1.len();
                    d1.swap(i1, j1);
                    v1.swap(i1, j1);
                }

                if !v2.is_empty() {
                    let j2 = j % v2.len();
                    let i2 = i % v2.len();
                    d2.swap(i2, j2);
                    v2.swap(i2, j2);
                }
            }
            &Op::SwapRemoveBack(i) => {
                assert_eq!(d1.swap_remove_back(i), v1.swap_remove_back(i));
                assert_eq!(d2.swap_remove_back(i), v2.swap_remove_back(i));

                if i > v1.len() + 1 && !v1.is_empty() {
                    let i1 = i % v1.len();
                    assert_eq!(d1.swap_remove_back(i1), v1.swap_remove_back(i1));
                }

                if i > v2.len() + 1 && !v2.is_empty() {
                    let i2 = i % v2.len();
                    assert_eq!(d1.swap_remove_back(i2), v1.swap_remove_back(i2));
                }
            }
            &Op::SwapRemoveFront(i) => {
                assert_eq!(d1.swap_remove_front(i), v1.swap_remove_front(i));
                assert_eq!(d2.swap_remove_front(i), v2.swap_remove_front(i));

                if i > v1.len() + 1 && !v1.is_empty() {
                    let i1 = i % v1.len();
                    assert_eq!(d1.swap_remove_front(i1), v1.swap_remove_front(i1));
                }

                if i > v2.len() + 1 && !v2.is_empty() {
                    let i2 = i % v2.len();
                    assert_eq!(d1.swap_remove_front(i2), v1.swap_remove_front(i2));
                }
            }
            &Op::Truncate(i) => {
                d1.truncate(i);
                v1.truncate(i);
                d2.truncate(i);
                v2.truncate(i);
            }
        }
    }
}
