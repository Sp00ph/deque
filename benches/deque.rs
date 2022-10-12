use criterion::{black_box, criterion_group, criterion_main, Criterion};
// use std::collections::VecDeque;
use deque::Deque as VecDeque;

fn criterion_benchmarks(c: &mut Criterion) {
    c.bench_function("bench_new", |b| {
        b.iter(|| {
            let ring: VecDeque<i32> = VecDeque::new();
            black_box(ring);
        })
    });

    c.bench_function("bench_grow_1025", |b| {
        b.iter(|| {
            let mut deq = VecDeque::new();
            for i in 0..1025 {
                deq.push_front(i);
            }
            black_box(deq);
        })
    });

    let ring: VecDeque<_> = (0..1000).collect();
    c.bench_function("bench_iter_1000", |b| {
        b.iter(|| {
            let mut sum = 0;
            for &i in &ring {
                sum += i;
            }
            black_box(sum);
        })
    });

    let mut ring: VecDeque<_> = (0..1000).collect();
    c.bench_function("bench_mut_iter_1000", |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in &mut ring {
                sum += *i;
            }
            black_box(sum);
        })
    });

    let ring: VecDeque<_> = (0..1000).collect();
    c.bench_function("bench_try_fold", |b| {
        b.iter(|| black_box(ring.iter().try_fold(0, |a, b| Some(a + b))))
    });

    const N: usize = 1000;
    let mut array: [usize; N] = [0; N];
    for i in 0..N {
        array[i] = i;
    }
    c.bench_function("bench_from_array_1000", |b| {
        b.iter(|| {
            let deq: VecDeque<_> = array.into();
            black_box(deq);
        })
    });

    let mut ring: VecDeque<u8> = VecDeque::with_capacity(1000);
    let input: &[u8] = &[128; 512];
    c.bench_function("bench_extend_bytes", |b| {
        b.iter(|| {
            ring.clear();
            ring.extend(black_box(input));
        })
    });

    let mut ring: VecDeque<u8> = VecDeque::with_capacity(1000);
    let input = vec![128; 512];
    c.bench_function("bench_extend_vec", |b| {
        b.iter(|| {
            ring.clear();

            let input = input.clone();
            ring.extend(black_box(input));
        })
    });

    let mut ring: VecDeque<u16> = VecDeque::with_capacity(1000);
    c.bench_function("bench_extend_trustedlen", |b| {
        b.iter(|| {
            ring.clear();
            ring.extend(black_box(0..512));
        })
    });

    let mut ring: VecDeque<u16> = VecDeque::with_capacity(1000);
    c.bench_function("bench_extend_chained_trustedlen", |b| {
        b.iter(|| {
            ring.clear();
            ring.extend(black_box((0..256).chain(768..1024)));
        })
    });

    let mut ring: VecDeque<u16> = VecDeque::with_capacity(1000);
    let input1: &[u16] = &[128; 256];
    let input2: &[u16] = &[255; 256];
    c.bench_function("bench_extend_chained_bytes", |b| {
        b.iter(|| {
            ring.clear();
            ring.extend(black_box(input1.iter().chain(input2.iter())));
        })
    });
}

criterion_group!(benches, criterion_benchmarks);
criterion_main!(benches);
