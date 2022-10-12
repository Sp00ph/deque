// #![feature(bench_black_box)]

// use std::{collections::VecDeque, time::Instant};


// use deque::Deque;
use std::collections::VecDeque as Deque;


fn main() {
    let mut d = Deque::new();
    for _ in 0..10_000_000 {
        d.clear();
        d.extend(std::hint::black_box((0..256).chain(768..1024)));
    }
}
