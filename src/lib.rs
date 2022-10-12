#![feature(
    allocator_api,
    slice_range,
    trusted_len,
    iter_advance_by,
    extend_one,
    min_specialization,
    std_internals,
    try_trait_v2
)]

extern crate alloc;

use alloc::{
    alloc::{handle_alloc_error, Allocator, Global, Layout},
    vec::Vec,
};

use std::io;

use core::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::{self, ByRefSized, FusedIterator, TrustedLen},
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ops::{Index, IndexMut, Range, RangeBounds, Try},
    ptr::{self, NonNull},
    slice,
};

pub struct Deque<T, A: Allocator = Global> {
    buf: NonNull<T>,
    cap: usize,
    head: usize,
    len: usize,
    alloc: A,
    _marker: PhantomData<T>,
}

impl<T> Deque<T> {
    #[inline]
    pub const fn new() -> Self {
        Self::new_in(Global)
    }

    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Self::with_capacity_in(cap, Global)
    }
}

impl<T, A: Allocator> Deque<T, A> {
    const MIN_NON_ZERO_CAP: usize = if mem::size_of::<T>() == 1 {
        8
    } else if mem::size_of::<T>() <= 1024 {
        4
    } else {
        1
    };

    #[inline]
    pub const fn new_in(alloc: A) -> Self {
        let cap = if mem::size_of::<T>() == 0 { usize::MAX } else { 0 };
        Self { buf: NonNull::dangling(), cap, head: 0, len: 0, alloc, _marker: PhantomData }
    }

    #[inline]
    pub fn with_capacity_in(cap: usize, alloc: A) -> Self {
        let mut this = Self::new_in(alloc);
        this.reserve_exact(cap);
        this
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub const fn capacity(&self) -> usize {
        self.cap
    }

    // this will never panic, as self.cap >= self.len is guaranteed.
    #[inline]
    pub const fn is_contiguous(&self) -> bool {
        self.head <= self.cap - self.len
    }

    #[inline]
    pub fn as_slices(&self) -> (&[T], &[T]) {
        let ptr = self.buf.as_ptr();
        if self.is_contiguous() {
            let slice = unsafe { slice::from_raw_parts(ptr.add(self.head), self.len) };
            (slice, &[])
        } else {
            // avoid the branch in self.tail() as we already know that we're not contiguous
            let cap = self.cap;
            let tail = self.head + self.len - cap;
            let slice1 = unsafe { slice::from_raw_parts(ptr.add(self.head), cap - self.head) };
            let slice2 = unsafe { slice::from_raw_parts(ptr, tail) };
            (slice1, slice2)
        }
    }

    #[inline]
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        let ptr = self.buf.as_ptr();
        if self.is_contiguous() {
            let slice = unsafe { slice::from_raw_parts_mut(ptr.add(self.head), self.len) };
            (slice, &mut [])
        } else {
            // avoid the branch in self.tail() as we already know that we're not contiguous
            let cap = self.cap;
            let tail = self.head + self.len - cap;
            let slice1 = unsafe { slice::from_raw_parts_mut(ptr.add(self.head), cap - self.head) };
            let slice2 = unsafe { slice::from_raw_parts_mut(ptr, tail) };
            (slice1, slice2)
        }
    }

    #[inline]
    pub fn front(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { &*self.front_ptr() })
        }
    }

    #[inline]
    pub fn back(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { &*self.back_ptr() })
        }
    }

    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { &mut *self.front_ptr() })
        }
    }

    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { &mut *self.back_ptr() })
        }
    }

    /// SAFETY: May only be called if self isn't empty.
    /// If acquired through a const ref, the returned pointer
    /// may not be used to mutate the element
    #[inline]
    unsafe fn front_ptr(&self) -> *mut T {
        self.buf.as_ptr().add(self.head)
    }

    /// SAFETY: May only be called if self isn't empty.
    /// If acquired through a const ref, the returned pointer
    /// may not be used to mutate the element
    #[inline]
    unsafe fn back_ptr(&self) -> *mut T {
        // let back_idx = self.head + self.len - 1;
        let (back_idx, overflow) = self.head.overflowing_add(self.len - 1);
        let back_idx = if overflow || back_idx >= self.cap {
            back_idx.wrapping_sub(self.cap)
        } else {
            back_idx
        };
        self.buf.as_ptr().add(back_idx)
    }

    /// Note that idx must be in the range of [0..self.cap) for this to work properly
    #[inline]
    fn wrap_idx(&self, idx: usize) -> usize {
        // we calculate the index in a bit of a funky way to avoid
        // any overflow errors which might potentially cause correctness
        // bugs on ZSTs
        if idx < self.cap - self.head {
            self.head + idx
        } else {
            self.head.wrapping_add(idx).wrapping_sub(self.cap)
        }
    }

    /// # Safety:
    /// idx must be smaller than self.cap
    #[inline]
    unsafe fn ptr_at_idx(&self, idx: usize) -> *mut T {
        self.buf.as_ptr().add(self.wrap_idx(idx))
    }

    #[inline]
    fn tail(&self) -> usize {
        self.wrap_idx(self.len)
    }

    pub fn reserve(&mut self, additional: usize) {
        let new_cap = self.len.checked_add(additional).expect("capacity overflow");
        if new_cap > self.cap {
            // if T is a ZST then self.cap == usize::MAX, so new_cap can't be greater than self.cap

            // since T is not a ZST, self.cap <= isize::MAX so self.cap * 2 can't overflow
            let new_cap = (self.cap * 2).max(new_cap).max(Self::MIN_NON_ZERO_CAP);
            unsafe { self.grow_to(new_cap) }
        }
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        let new_cap = self.len.checked_add(additional).expect("capacity overflow");
        if new_cap > self.cap {
            // if T is a ZST then self.cap == usize::MAX, so new_cap can't be greater than self.cap

            // since T is not a ZST, self.cap <= isize::MAX so self.cap * 2 can't overflow
            unsafe { self.grow_to(new_cap) }
        }
    }

    #[inline]
    fn reserve_for_push(&mut self) {
        if self.len == self.cap {
            if mem::size_of::<T>() == 0 {
                panic!("capacity overflow");
            } else {
                // SAFETY: we just confirmed that T is not a ZST. Also,
                // for any T that is not a ZST, the capacity is at most isize::MAX,
                // so the multiplication can never overflow, which means the new capacity
                // will always be greater than the old one (if self.cap == 0 then new_cap
                // will be MIN_NON_ZERO_CAP which as the name implies is greater than 0)
                unsafe { self.grow_to((self.cap * 2).max(Self::MIN_NON_ZERO_CAP)) }
            }
        }
    }

    #[inline]
    pub fn push_back(&mut self, val: T) {
        self.reserve_for_push();

        // at this point it's guaranteed that self.cap > self.len so there's space at self.tail

        // SAFETY: there's guaranteed to be free space at self.tail
        unsafe { self.buf.as_ptr().add(self.tail()).write(val) };
        self.len += 1;
    }

    #[inline]
    pub fn push_front(&mut self, val: T) {
        self.reserve_for_push();

        let new_head = self.head.checked_sub(1).unwrap_or(self.cap - 1);

        // SAFETY: due to the call to reserve_for_push() there's guaranteed to be space before self.head
        unsafe { self.buf.as_ptr().add(new_head).write(val) };
        self.head = new_head;
        self.len += 1;
    }

    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        // We wrap the read value in a ManuallyDrop just in case something unwinds before we
        // updated everything
        let val = ManuallyDrop::new(unsafe { self.buf.as_ptr().add(self.head).read() });
        self.len -= 1;
        self.head = if self.head == self.cap - 1 { 0 } else { self.head + 1 };

        Some(ManuallyDrop::into_inner(val))
    }

    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let new_tail = self.tail().checked_sub(1).unwrap_or(self.cap - 1);

        let val = ManuallyDrop::new(unsafe { self.buf.as_ptr().add(new_tail).read() });
        self.len -= 1;

        Some(ManuallyDrop::into_inner(val))
    }

    /// # Safety
    /// `new_cap` must be greater than `self.cap`
    #[cold]
    unsafe fn grow_to(&mut self, new_cap: usize) {
        let layout = Self::array_layout(new_cap);

        if self.cap == 0 {
            self.buf =
                self.alloc.allocate(layout).unwrap_or_else(|_| handle_alloc_error(layout)).cast();
            self.cap = new_cap;
            return;
        }

        // Safety: Because we already have this layout in memory, a layout
        // overflow is impossible, so we don't have to check for it.
        let cur_layout = Self::array_layout_unchecked(self.cap);

        // from now on we need to be pretty careful, as we must not unwind until all the items are copied over
        // and the capacity field is updated, otherwise the destructor would invoke UB, so we can never panic
        // until then.
        self.buf = self
            .alloc
            .grow(self.buf.cast(), cur_layout, layout)
            .unwrap_or_else(|_| handle_alloc_error(layout))
            .cast();

        // is_contiguous() never panics
        if !self.is_contiguous() {
            // new_cap > self.cap is guaranteed by the function preconditions.
            let shift = new_cap - self.cap;
            let head_len = self.cap - self.head;
            let head_ptr = self.buf.as_ptr().add(self.head);

            ptr::copy(head_ptr, head_ptr.add(shift), head_len);

            self.head += shift;
        }

        self.cap = new_cap;
    }

    #[inline]
    fn array_layout(len: usize) -> Layout {
        match Layout::array::<T>(len) {
            Ok(l) if l.size() <= isize::MAX as _ => l,
            _ => panic!("capacity overflow"),
        }
    }

    #[inline]
    unsafe fn array_layout_unchecked(len: usize) -> Layout {
        Layout::from_size_align_unchecked(mem::size_of::<T>() * len, mem::align_of::<T>())
    }

    fn head_room(&self) -> usize {
        if self.is_contiguous() {
            self.cap - self.len - self.head
        } else {
            self.cap - self.len
        }
    }

    /// # Safety
    /// Callers must ensure that `self.len + slice.len() <= self.cap`
    /// This function is guaranteed to never panic.
    unsafe fn append_slice(&mut self, slice: &[T]) {
        let tail = self.tail();
        let tail_ptr = self.buf.as_ptr().add(tail);
        let head_room = self.head_room();

        // note that if !self.is_contiguous(), then this branch is always taken
        // due to the function precondition.
        if slice.len() <= head_room {
            ptr::copy_nonoverlapping(slice.as_ptr(), tail_ptr, slice.len());
        } else {
            ptr::copy_nonoverlapping(slice.as_ptr(), tail_ptr, head_room);
            ptr::copy_nonoverlapping(
                slice.as_ptr().add(head_room),
                self.buf.as_ptr(),
                slice.len() - head_room,
            );
        }
        self.len += slice.len();
    }

    /// # Safety
    /// `[from..from+len)` and `[to..to+len)` must lie inside `[0..2*self.cap)` and `len <= self.len()`
    unsafe fn copy_range_internal(&mut self, from: usize, to: usize, len: usize) {
        // if src < dst {
        //     for i in 0..len {
        //         ptr::copy_nonoverlapping(self.ptr_at_idx(src + i), self.ptr_at_idx(dst + i), 1);
        //     }
        // } else {
        //     for i in (0..len).rev() {
        //         ptr::copy_nonoverlapping(self.ptr_at_idx(src + i), self.ptr_at_idx(dst + i), 1);
        //     }
        // }

        let (src, dst) = (self.wrap_idx(from), self.wrap_idx(to));
        // We special case ZSTs here, as they dont need any actual memory to be copied around.
        // This way, we can be sure that `self.cap`, `self.head`, `from` and `to` are at most isize::MAX and
        // `len` is at most isize::MAX per the preconditions.
        if mem::size_of::<T>() == 0 || src == dst || len == 0 {
            return;
        }

        let src_pre_wrap = self.cap - src;
        let dst_pre_wrap = self.cap - dst;
        let src_wraps = src_pre_wrap < len;
        let dst_wraps = dst_pre_wrap < len;

        let dst_after_src = {
            let (wrapped, carry) = dst.overflowing_sub(src);
            let diff = if carry { wrapped.wrapping_add(self.cap) } else { wrapped };
            diff < len
        };

        let buf = self.buf.as_ptr();

        let copy = move |src: usize, dst: usize, len: usize| {
            ptr::copy(buf.add(src), buf.add(dst), len);
        };

        match (dst_after_src, src_wraps, dst_wraps) {
            (true, true, true) => {
                let delta = src_pre_wrap - dst_pre_wrap;

                copy(0, delta, len - src_pre_wrap);
                copy(src + dst_pre_wrap, 0, delta);
                copy(src, dst, dst_pre_wrap);
            }
            (true, true, false) => {
                copy(0, dst + src_pre_wrap, len - src_pre_wrap);
                copy(src, dst, src_pre_wrap);
            }
            (true, false, true) => {
                copy(src + dst_pre_wrap, 0, len - dst_pre_wrap);
                copy(src, dst, dst_pre_wrap);
            }
            (false, true, true) => {
                let delta = dst_pre_wrap - src_pre_wrap;

                copy(src, dst, src_pre_wrap);
                copy(0, dst + src_pre_wrap, delta);
                copy(delta, 0, len - dst_pre_wrap);
            }
            (false, true, false) => {
                copy(src, dst, src_pre_wrap);
                copy(0, dst + src_pre_wrap, len - src_pre_wrap);
            }
            (false, false, true) => {
                copy(src, dst, dst_pre_wrap);
                copy(src + dst_pre_wrap, 0, len - dst_pre_wrap);
            }
            (_, false, false) => {
                copy(src, dst, len);
            }
        }
    }

    pub fn make_contiguous(&mut self) -> &mut [T] {
        // if T is a ZST, we don't need to do any actual copying
        if mem::size_of::<T>() == 0 {
            self.head = 0;
        }
        if self.is_contiguous() {
            unsafe { return slice::from_raw_parts_mut(self.front_ptr(), self.len) }
        }

        let &mut Self { buf, cap, head, len, .. } = self;
        let ptr = buf.as_ptr();

        let free = cap - len;
        let head_len = cap - head;
        let tail = len - head_len;
        let tail_len = tail;

        if free >= head_len {
            // there is enough free space to copy the head in one go,
            // this means that we first shift the tail backwards, and then
            // copy the head to the correct position.
            //
            // from: DEFGH....ABC
            // to:   ABCDEFGH....

            unsafe {
                ptr::copy(ptr, ptr.add(head_len), tail_len);
                // ...DEFGH.ABC
                ptr::copy_nonoverlapping(ptr.add(head), ptr, head_len);
                // ABCDEFGH....
            }

            self.head = 0;
        } else if free >= tail_len {
            // there is enough free space to copy the tail in one go,
            // this means that we first shift the head forwards, and then
            // copy the tail to the correct position.
            //
            // from: FGH....ABCDE
            // to:   ...ABCDEFGH.

            unsafe {
                ptr::copy(ptr.add(head), ptr.add(tail), head_len);
                // FGHABCDE....
                ptr::copy_nonoverlapping(ptr, ptr.add(tail + head_len), tail_len);
                // ...ABCDEFGH.
            }

            self.head = tail;
        } else {
            // FGH..ABCDE
            //

            let (mut left_edge, mut right_edge) = (0, head);

            while left_edge < len && right_edge != cap {
                let mut right_offset = 0;
                for i in left_edge..right_edge {
                    right_offset = (i - left_edge) % (cap - right_edge);
                    let src = right_edge + right_offset;
                    unsafe { ptr::swap(ptr.add(i), ptr.add(src)) };
                }
                let n_ops = right_edge - left_edge;
                left_edge += n_ops;
                right_edge += right_offset + 1;
            }

            self.head = 0;
        }

        unsafe { slice::from_raw_parts_mut(self.front_ptr(), self.len) }
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        let (a, b) = self.as_slices();
        Iter { i1: a.iter(), i2: b.iter() }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        let (a, b) = self.as_mut_slices();
        IterMut { i1: a.iter_mut(), i2: b.iter_mut() }
    }

    #[inline]
    pub const fn allocator(&self) -> &A {
        &self.alloc
    }

    pub fn append(&mut self, other: &mut Self) {
        self.reserve(other.len);
        let (a, b) = other.as_slices();
        // Safety: other.len == a.len() + b.len(), so the reserve ensures
        // that the capacity is sufficient. also, append_slice() should never panic,
        // so double frees shouldn't happen
        unsafe {
            self.append_slice(a);
            self.append_slice(b);
        }
        other.len = 0;
    }

    #[inline]
    pub fn retain<F: FnMut(&T) -> bool>(&mut self, mut f: F) {
        self.retain_mut(|t| f(t))
    }

    pub fn retain_mut<F: FnMut(&mut T) -> bool>(&mut self, mut f: F) {
        let len = self.len();
        let mut idx = 0;
        let mut cur = 0;

        while cur < len {
            if !f(unsafe { self.get_unchecked_mut(cur) }) {
                cur += 1;
                break;
            }
            cur += 1;
            idx += 1;
        }

        while cur < len {
            if !f(unsafe { self.get_unchecked_mut(cur) }) {
                cur += 1;
                continue;
            }

            unsafe { self.swap_unchecked(cur, idx) };
            cur += 1;
            idx += 1;
        }

        if cur != idx {
            self.truncate(idx);
        }
    }

    #[inline]
    pub fn get(&self, idx: usize) -> Option<&T> {
        if idx >= self.len {
            None
        } else {
            Some(unsafe { self.get_unchecked(idx) })
        }
    }

    /// # Safety
    /// Callers must ensure that `idx < self.len()`.
    #[inline]
    pub unsafe fn get_unchecked(&self, idx: usize) -> &T {
        &*self.buf.as_ptr().add(self.wrap_idx(idx))
    }

    #[inline]
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        if idx >= self.len {
            None
        } else {
            Some(unsafe { self.get_unchecked_mut(idx) })
        }
    }

    /// # Safety
    /// Callers must ensure that `idx < self.len()`.
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, idx: usize) -> &mut T {
        &mut *self.ptr_at_idx(idx)
    }

    #[inline]
    pub fn swap(&mut self, i: usize, j: usize) {
        if i >= self.len || j >= self.len {
            panic!(
                "swap indices out of bounds: tried to swap {i} and {j} on a Deque of length {}",
                self.len
            );
        }
        unsafe { self.swap_unchecked(i, j) }
    }

    /// # Safety
    /// `i` and `j` must be smaller than `self.len()`
    #[inline]
    pub unsafe fn swap_unchecked(&mut self, i: usize, j: usize) {
        ptr::swap(self.ptr_at_idx(i), self.ptr_at_idx(j))
    }

    #[inline]
    unsafe fn write_iter(&mut self, it: impl Iterator<Item = T>, idx: usize, written: &mut usize) {
        let ptr = unsafe { self.buf.as_ptr().add(idx) };
        it.enumerate().for_each(|(i, val)| {
            unsafe { ptr::write(ptr.add(i), val) };
            *written += 1;
        });
    }

    /// # Safety
    /// `self.len + len <= self.cap` must be true. returns the number of elements written.
    #[inline]
    unsafe fn write_iter_wrapping(&mut self, mut it: impl Iterator<Item = T>, len: usize) -> usize {
        struct Guard {
            len_ptr: *mut usize,
            written: usize,
        }

        impl Drop for Guard {
            fn drop(&mut self) {
                unsafe { *self.len_ptr += self.written }
            }
        }

        let mut guard = Guard { len_ptr: &mut self.len, written: 0 };

        let head_room = self.head_room();
        if len <= head_room {
            self.write_iter(it, self.head, &mut guard.written);
        } else {
            self.write_iter(ByRefSized(&mut it).take(head_room), self.head, &mut guard.written);
            self.write_iter(it.take(len - head_room), 0, &mut guard.written);
        }

        guard.written
    }

    pub fn truncate(&mut self, len: usize) {
        if len >= self.len {
            return;
        }
        if !mem::needs_drop::<T>() {
            self.len = len;
            return;
        }
        struct Dropper<T>(*mut [T]);
        impl<T> Drop for Dropper<T> {
            fn drop(&mut self) {
                unsafe { ptr::drop_in_place(self.0) }
            }
        }

        let (a, b) = self.as_mut_slices();
        if len <= a.len() {
            let a = &mut a[len..] as *mut _;
            let b = b as *mut _;
            self.len = len;
            let _dropper = Dropper(b);
            unsafe { ptr::drop_in_place(a) }
        } else {
            let len = len - a.len();
            let b = &mut b[len..] as *mut _;
            self.len = len;
            unsafe { ptr::drop_in_place(b) }
        }
    }

    #[inline]
    pub fn binary_search(&self, t: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.binary_search_by(|e| e.cmp(t))
    }

    #[inline]
    pub fn binary_search_by_key<'a, B: Ord, F: FnMut(&'a T) -> B>(
        &'a self,
        b: &B,
        mut f: F,
    ) -> Result<usize, usize> {
        self.binary_search_by(|e| f(e).cmp(b))
    }

    pub fn binary_search_by<'a, F: FnMut(&'a T) -> Ordering>(
        &'a self,
        mut f: F,
    ) -> Result<usize, usize> {
        let (front, back) = self.as_slices();

        match back.first().map(&mut f) {
            Some(Ordering::Equal) => Ok(front.len()),
            Some(Ordering::Less) => match back.binary_search_by(f) {
                Ok(i) => Ok(i + front.len()),
                Err(i) => Err(i + front.len()),
            },
            _ => front.binary_search_by(f),
        }
    }

    #[inline]
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&T) -> bool,
    {
        let (front, back) = self.as_slices();

        if let Some(true) = back.first().map(&mut pred) {
            back.partition_point(pred) + front.len()
        } else {
            front.partition_point(pred)
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
        self.head = 0;
    }

    #[inline]
    pub fn contains(&self, t: &T) -> bool
    where
        T: PartialEq,
    {
        let (a, b) = self.as_slices();
        a.contains(t) || b.contains(t)
    }

    #[inline]
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<'_, T, A> {
        let range = slice::range(range, ..self.len);
        let (start, len) = (range.start, range.end - range.start);
        let orig_len = mem::replace(&mut self.len, start);

        Drain {
            deque: self,
            orig_len,
            drain_start: start,
            drain_len: len,
            idx: start,
            remaining: len,
        }
    }

    pub fn insert(&mut self, idx: usize, val: T) {
        if idx > self.len {
            panic!("tried to insert at index {idx} into a deque of length {}", self.len);
        }
        self.reserve_for_push();
        let k = self.len - idx;
        if idx < k {
            // we know that the capacity is > 0 because of the call to reserve_for_push()
            self.head = self.head.checked_sub(1).unwrap_or(self.cap - 1);
            unsafe { self.copy_range_internal(1, 0, idx) }
        } else {
            unsafe { self.copy_range_internal(idx, idx + 1, k) }
        }
        unsafe { self.ptr_at_idx(idx).write(val) };
        self.len += 1;
    }

    fn slice_ranges<R: RangeBounds<usize>>(&self, r: R) -> (Range<usize>, Range<usize>) {
        let r = slice::range(r, ..self.len);
        let a_len = (self.cap - self.head).min(self.len);
        if r.end <= a_len {
            (r, 0..0)
        } else if r.start >= a_len {
            (0..0, r.start - a_len..r.end - a_len)
        } else {
            (r.start..a_len, 0..r.end - a_len)
        }
    }

    #[inline]
    pub fn range<R: RangeBounds<usize>>(&self, r: R) -> Iter<'_, T> {
        let (a_range, b_range) = self.slice_ranges(r);
        let (a, b) = self.as_slices();
        Iter { i1: a[a_range].iter(), i2: b[b_range].iter() }
    }

    #[inline]
    pub fn range_mut<R: RangeBounds<usize>>(&mut self, r: R) -> IterMut<'_, T> {
        let (a_range, b_range) = self.slice_ranges(r);
        let (a, b) = self.as_mut_slices();
        IterMut { i1: a[a_range].iter_mut(), i2: b[b_range].iter_mut() }
    }

    pub fn remove(&mut self, idx: usize) -> Option<T> {
        if idx >= self.len {
            return None;
        }

        let val = ManuallyDrop::new(unsafe { ptr::read(self.ptr_at_idx(idx)) });

        let k = self.len - idx;
        if idx < k {
            unsafe { self.copy_range_internal(0, 1, idx) };
            self.head = self.wrap_idx(1);
        } else {
            unsafe { self.copy_range_internal(idx + 1, idx, k) }
        }

        self.len -= 1;
        Some(ManuallyDrop::into_inner(val))
    }

    pub fn split_off(&mut self, at: usize) -> Deque<T, A>
    where
        A: Clone,
    {
        if at > self.len {
            panic!("tried to split a deque of length {} at index {at}", self.len);
        }

        let tail_len = self.len - at;
        let wrapped = self.wrap_idx(at);
        let mut result = Deque::with_capacity_in(tail_len, self.alloc.clone());

        self.len = at;

        if wrapped <= self.cap - tail_len {
            unsafe {
                result
                    .append_slice(slice::from_raw_parts(self.buf.as_ptr().add(wrapped), tail_len));
            }
        } else {
            let len1 = self.cap - wrapped;
            let len2 = tail_len - len1;
            unsafe {
                result.append_slice(slice::from_raw_parts(self.buf.as_ptr().add(wrapped), len1));
                result.append_slice(slice::from_raw_parts(self.buf.as_ptr(), len2));
            }
        }

        result.len = tail_len;
        result
    }

    #[inline]
    pub fn resize(&mut self, new_len: usize, val: T)
    where
        T: Clone,
    {
        self.resize_with(new_len, || val.clone())
    }

    #[inline]
    pub fn resize_with<F: FnMut() -> T>(&mut self, new_len: usize, generator: F) {
        if new_len > self.len {
            self.reserve(new_len - self.len);
            self.extend(iter::repeat_with(generator).take(new_len - self.len));
        } else {
            self.truncate(new_len);
        }
    }

    #[inline]
    pub fn rotate_left(&mut self, mid: usize) {
        assert!(mid <= self.len);
        let k = self.len - mid;
        if k < mid {
            unsafe { self.rotate_right_inner(k) }
        } else {
            unsafe { self.rotate_left_inner(mid) }
        }
    }

    #[inline]
    pub fn rotate_right(&mut self, mid: usize) {
        assert!(mid <= self.len);
        let k = self.len - mid;
        if k < mid {
            unsafe { self.rotate_left_inner(k) }
        } else {
            unsafe { self.rotate_right_inner(mid) }
        }
    }

    #[inline]
    unsafe fn rotate_left_inner(&mut self, mid: usize) {
        // 345012.
        if self.cap != self.len {
            self.copy_range_internal(0, self.len, mid);
        }
        self.head = self.wrap_idx(mid);
    }

    #[inline]
    unsafe fn rotate_right_inner(&mut self, mid: usize) {
        let (head, carry) = self.head.overflowing_sub(mid);
        self.head = if carry { head.wrapping_add(self.cap) } else { head };
        if self.cap != self.len {
            self.copy_range_internal(self.len, 0, mid);
        }
    }

    #[inline]
    pub fn swap_remove_back(&mut self, idx: usize) -> Option<T> {
        if idx >= self.len {
            return None;
        }

        self.len -= 1;
        unsafe {
            self.swap_unchecked(idx, self.len);
            Some(ptr::read(self.ptr_at_idx(self.len)))
        }
    }

    #[inline]
    pub fn swap_remove_front(&mut self, idx: usize) -> Option<T> {
        if idx >= self.len {
            return None;
        }

        self.len -= 1;
        unsafe {
            self.swap_unchecked(idx, 0);
            let val = ptr::read(self.ptr_at_idx(0));
            self.head = self.wrap_idx(1);
            Some(val)
        }
    }

    pub fn shrink_to(&mut self, min_capacity: usize) {
        let min_capacity = min_capacity.max(self.len).max(Self::MIN_NON_ZERO_CAP);

        if mem::size_of::<T>() == 0 || self.cap <= min_capacity {
            return;
        }

        // set the length field to 0 for the duration of the method, to avoid
        // any troubles if anything happens to unwind.
        let len = mem::replace(&mut self.len, 0);
        let buf = self.buf.as_ptr();
        // we already know that T isn't a ZST, so `self.head <= isize::MAX` and `len <= isize::MAX`
        // => the addition can't overflow
        if self.head + len <= min_capacity {
            if self.head == min_capacity {
                self.head = 0;
            }
            // nothing to copy in this case
        } else if self.head >= min_capacity {
            if self.head + len <= self.cap {
                // all the elements are beyond min_capacity, and the deque is contiguous

                // since head >= min_capacity and min_capacity >= len, we know that the src and dst dont overlap
                unsafe { ptr::copy_nonoverlapping(buf.add(self.head), buf, len) };
                self.head = 0;
            } else {
                // only some elements are beyond min_capacity, copy them to just before min_capacity

                // EFG......ABCD => EFG..ABCD.... => EFG..ABCD
                let head_len = self.cap - self.head;
                let new_head = min_capacity - head_len;
                unsafe { ptr::copy(buf.add(self.head), buf.add(new_head), head_len) };
                self.head = new_head;
            }
        } else {
            // head is in bounds but some items arent and need to be copied to the front.

            if self.head + len <= self.cap {
                // ...ABCDE.. => DE.ABC.... => DE.ABC

                // this won't overflow as its handled by the first if condition
                let tail_len = self.head + len - min_capacity;

                unsafe { ptr::copy_nonoverlapping(buf.add(min_capacity), buf, tail_len) }
            } else {
                // DE...ABC => ..DE.ABC => BCDE.A.. => BCDE.A
                let len1 = self.cap - min_capacity;
                let len2 = len - (self.cap - self.head);
                unsafe {
                    ptr::copy(buf, buf.add(len1), len2);
                    ptr::copy(buf.add(min_capacity), buf, len1);
                }
            }
        }

        let old_layout = unsafe { Self::array_layout_unchecked(self.cap) };
        // we know that min_capacity < self.cap, so the layout can't overflow
        let new_layout = unsafe { Self::array_layout_unchecked(min_capacity) };

        self.buf = unsafe { self.alloc.shrink(self.buf.cast(), old_layout, new_layout) }
            .unwrap_or_else(|_| handle_alloc_error(new_layout))
            .cast();
        self.cap = min_capacity;
        self.len = len;
    }

    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0)
    }
}

impl<T, A: Allocator> Drop for Deque<T, A> {
    fn drop(&mut self) {
        struct DeallocGuard<A: Allocator> {
            ptr: NonNull<u8>,
            layout: Layout,
            // We can't just use a &A, as that would interfere with
            // the call to self.clear(), but self.clear() never uses
            // the allocator and we never move self anywhere else,
            // so using a raw pointer like this should be fine.
            alloc: *const A,
        }

        impl<A: Allocator> Drop for DeallocGuard<A> {
            fn drop(&mut self) {
                if self.layout.size() != 0 {
                    unsafe { (*self.alloc).deallocate(self.ptr.cast(), self.layout) };
                }
            }
        }

        let layout = unsafe { Self::array_layout_unchecked(self.cap) };

        let _guard = DeallocGuard { ptr: self.buf.cast(), layout, alloc: &self.alloc };

        if mem::needs_drop::<T>() {
            struct Dropper<'a, T>(&'a mut [T]);

            impl<'a, T> Drop for Dropper<'a, T> {
                fn drop(&mut self) {
                    unsafe { ptr::drop_in_place(self.0) }
                }
            }

            let (a, b) = self.as_mut_slices();
            let _back_dropper = Dropper(b);
            unsafe { ptr::drop_in_place(a) };
        }
    }
}

impl<T, A: Allocator> From<Vec<T, A>> for Deque<T, A> {
    fn from(v: Vec<T, A>) -> Self {
        let (buf, len, cap, alloc) = v.into_raw_parts_with_alloc();
        // currently, Vec<T> already has a capacity of usize::MAX if T is a ZST, but i just
        // want to absolutely ensure it, as the implementation heavily relies on self.cap being
        // usize::MAX for ZSTs.
        let cap = if mem::size_of::<T>() == 0 { usize::MAX } else { cap };
        Self {
            buf: unsafe { NonNull::new_unchecked(buf) },
            len,
            cap,
            alloc,
            head: 0,
            _marker: PhantomData,
        }
    }
}

impl<T, A: Allocator> From<Deque<T, A>> for Vec<T, A> {
    fn from(mut d: Deque<T, A>) -> Self {
        let ptr = d.make_contiguous().as_ptr();
        let d = ManuallyDrop::new(d);
        unsafe { ptr::copy(ptr, d.buf.as_ptr(), d.len) };
        let buf = d.buf.as_ptr();
        let len = d.len;
        let cap = d.cap;
        let alloc = unsafe { ptr::read(&d.alloc) };
        unsafe { Vec::from_raw_parts_in(buf, len, cap, alloc) }
    }
}

impl<T, const N: usize> From<[T; N]> for Deque<T> {
    #[inline]
    fn from(arr: [T; N]) -> Self {
        let arr = ManuallyDrop::new(arr);
        let mut this = Self::with_capacity(arr.len());
        unsafe {
            ptr::copy_nonoverlapping(arr.as_ptr(), this.buf.as_ptr(), arr.len());
        }
        this.len = arr.len();
        this
    }
}

trait SpecExtend<T, I: Iterator<Item = T>> {
    fn spec_extend(&mut self, iter: I);
}

impl<T, A: Allocator> Extend<T> for Deque<T, A> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        SpecExtend::spec_extend(self, iter.into_iter());
    }

    #[inline]
    fn extend_one(&mut self, item: T) {
        self.push_back(item)
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional)
    }
}

impl<T, A: Allocator, I: Iterator<Item = T>> SpecExtend<T, I> for Deque<T, A> {
    #[inline]
    default fn spec_extend(&mut self, mut iter: I) {
        loop {
            let room = self.cap - self.len;
            let written = unsafe { self.write_iter_wrapping(ByRefSized(&mut iter).take(room), room) };
            match iter.next() {
                Some(t) => {
                    self.reserve(iter.size_hint().0.saturating_add(1));
                    self.push_back(t)
                },
                None => return
            }
        }
    }
}

impl<T, A: Allocator, I: Iterator<Item = T> + TrustedLen> SpecExtend<T, I> for Deque<T, A> {
    #[inline]
    fn spec_extend(&mut self, iter: I) {
        let len = match iter.size_hint().1 {
            Some(a) => a,
            // in this case iter contains at least usize::MAX elements, so
            // don't even bother trying to push them all.
            None => {
                panic!("capacity overflow")
            }
        };
        self.reserve(len);
        unsafe { self.write_iter_wrapping(iter, len) };
    }
}

impl<'a, T: 'a + Copy, A: Allocator> Extend<&'a T> for Deque<T, A> {
    #[inline]
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().copied())
    }

    #[inline]
    fn extend_one(&mut self, item: &'a T) {
        self.push_back(*item)
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional)
    }
}

impl<T> FromIterator<T> for Deque<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from(Vec::from_iter(iter))
    }
}

impl<T: fmt::Debug, A: Allocator> fmt::Debug for Deque<T, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Clone, A: Allocator + Clone> Clone for Deque<T, A> {
    #[inline]
    fn clone(&self) -> Self {
        let mut vec = Vec::with_capacity_in(self.len, self.alloc.clone());
        let (a, b) = self.as_slices();
        vec.extend_from_slice(a);
        vec.extend_from_slice(b);
        Self::from(vec)
    }
}

impl<T> Default for Deque<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: PartialEq<U>, U, A: Allocator, B: Allocator> PartialEq<Deque<U, B>> for Deque<T, A> {
    fn eq(&self, other: &Deque<U, B>) -> bool {
        if self.len != other.len {
            return false;
        }
        let (a, b) = self.as_slices();
        let (c, d) = other.as_slices();
        match a.len().cmp(&c.len()) {
            Ordering::Equal => a == c && b == d,
            Ordering::Less => {
                let front = a.len();
                let mid = c.len() - front;
                let (c_front, c_mid) = c.split_at(front);
                let (b_mid, b_back) = b.split_at(mid);
                a == c_front && b_mid == c_mid && b_back == d
            }
            Ordering::Greater => {
                let front = c.len();
                let mid = a.len() - front;
                let (a_front, a_mid) = a.split_at(front);
                let (d_mid, d_back) = d.split_at(mid);
                a_front == c && a_mid == d_mid && b == d_back
            }
        }
    }
}

impl<T: PartialEq<U>, U, A: Allocator> PartialEq<[U]> for Deque<T, A> {
    #[inline]
    fn eq(&self, other: &[U]) -> bool {
        if self.len != other.len() {
            return false;
        }
        let (a, b) = self.as_slices();
        let (c, d) = other.split_at(a.len());
        a == c && b == d
    }
}

impl<T: PartialEq<U>, U, A: Allocator, const N: usize> PartialEq<[U; N]> for Deque<T, A> {
    #[inline]
    fn eq(&self, other: &[U; N]) -> bool {
        self == other.as_slice()
    }
}

impl<T: PartialOrd, A: Allocator> PartialOrd for Deque<T, A> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord, A: Allocator> Ord for Deque<T, A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T: Eq, A: Allocator> Eq for Deque<T, A> {}

impl<T: Hash, A: Allocator> Hash for Deque<T, A> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.len);
        self.iter().for_each(|t| t.hash(state));
    }
}

impl<T, A: Allocator> Index<usize> for Deque<T, A> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("Out of bounds access")
    }
}

impl<T, A: Allocator> IndexMut<usize> for Deque<T, A> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).expect("Out of bounds access")
    }
}

unsafe impl<T: Send, A: Allocator + Send> Send for Deque<T, A> {}

unsafe impl<T: Sync, A: Allocator + Sync> Sync for Deque<T, A> {}

impl<A: Allocator> io::Write for Deque<u8, A> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.reserve(buf.len());
        unsafe { self.append_slice(buf) };
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.write(buf).map(|_| ())
    }
}

impl<A: Allocator> io::Read for Deque<u8, A> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let (a, _) = self.as_slices();
        let (a_len, buf_len) = (a.len(), buf.len());
        if a_len > buf_len {
            buf.copy_from_slice(&a[..buf_len]);
            self.head += buf_len;
            self.len -= buf_len;
            Ok(buf_len)
        } else {
            buf[..a_len].copy_from_slice(a);
            self.head = 0;
            self.len -= a_len;
            Ok(a_len)
        }
    }

    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        let len = self.len;
        let (a, b) = self.as_slices();
        buf.extend_from_slice(a);
        buf.extend_from_slice(b);
        self.len = 0;
        Ok(len)
    }

    fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<()> {
        let n = self.read(buf)?;
        if n == buf.len() {
            return Ok(());
        }
        let rem = buf.len() - n;
        let m = self.read(&mut buf[rem..])?;
        if m == rem {
            Ok(())
        } else {
            Err(io::Error::from(io::ErrorKind::UnexpectedEof))
        }
    }
}

impl<T, A: Allocator> IntoIterator for Deque<T, A> {
    type Item = T;

    type IntoIter = IntoIter<T, A>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

impl<'a, T, A: Allocator> IntoIterator for &'a Deque<T, A> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, A: Allocator> IntoIterator for &'a mut Deque<T, A> {
    type Item = &'a mut T;

    type IntoIter = IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct Iter<'a, T> {
    i1: slice::Iter<'a, T>,
    i2: slice::Iter<'a, T>,
}

pub struct IterMut<'a, T> {
    i1: slice::IterMut<'a, T>,
    i2: slice::IterMut<'a, T>,
}

#[derive(Clone, Debug)]
pub struct IntoIter<T, A: Allocator>(Deque<T, A>);

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.i1.next() {
            Some(t) => Some(t),
            None => {
                mem::swap(&mut self.i1, &mut self.i2);
                self.i1.next()
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    #[inline]
    fn advance_by(&mut self, n: usize) -> Result<(), usize> {
        let m = match self.i1.advance_by(n) {
            Ok(_) => return Ok(()),
            Err(m) => m,
        };
        mem::swap(&mut self.i1, &mut self.i2);
        self.i1.advance_by(n - m).map_err(|o| o + m)
    }

    #[inline]
    fn all<F>(&mut self, mut f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        self.i1.all(&mut f) && self.i2.all(f)
    }

    #[inline]
    fn any<F>(&mut self, mut f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        self.i1.any(&mut f) || self.i2.any(f)
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len()
    }

    #[inline]
    fn find<P>(&mut self, mut predicate: P) -> Option<Self::Item>
    where
        Self: Sized,
        P: FnMut(&Self::Item) -> bool,
    {
        self.i1.find(&mut predicate).or_else(|| self.i2.find(predicate))
    }

    #[inline]
    fn find_map<B, F>(&mut self, mut f: F) -> Option<B>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> Option<B>,
    {
        self.i1.find_map(&mut f).or_else(|| self.i2.find_map(f))
    }

    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let accum = self.i1.fold(init, &mut f);
        self.i2.fold(accum, f)
    }

    #[inline]
    fn for_each<F>(self, mut f: F)
    where
        Self: Sized,
        F: FnMut(Self::Item),
    {
        self.i1.for_each(&mut f);
        self.i2.for_each(f);
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    #[inline]
    fn max_by<F>(self, mut compare: F) -> Option<Self::Item>
    where
        Self: Sized,
        F: FnMut(&Self::Item, &Self::Item) -> Ordering,
    {
        let (m1, m2) = match (self.i1.max_by(&mut compare), self.i2.max_by(&mut compare)) {
            (None, None) => return None,
            (None, Some(max)) | (Some(max), None) => return Some(max),
            (Some(m1), Some(m2)) => (m1, m2),
        };
        match compare(&m1, &m2) {
            Ordering::Less => Some(m2),
            _ => Some(m1),
        }
    }

    #[inline]
    fn min_by<F>(self, mut compare: F) -> Option<Self::Item>
    where
        Self: Sized,
        F: FnMut(&Self::Item, &Self::Item) -> Ordering,
    {
        let (m1, m2) = match (self.i1.min_by(&mut compare), self.i2.min_by(&mut compare)) {
            (None, None) => return None,
            (None, Some(min)) | (Some(min), None) => return Some(min),
            (Some(m1), Some(m2)) => (m1, m2),
        };
        match compare(&m1, &m2) {
            Ordering::Greater => Some(m2),
            _ => Some(m1),
        }
    }

    #[inline]
    fn position<P>(&mut self, mut predicate: P) -> Option<usize>
    where
        Self: Sized,
        P: FnMut(Self::Item) -> bool,
    {
        let len1 = self.i1.len();
        if let Some(i) = self.i1.position(&mut predicate) {
            return Some(i);
        }
        mem::swap(&mut self.i1, &mut self.i2);
        self.i1.position(predicate).map(|i| i + len1)
    }

    #[inline]
    fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        let b = self.i1.try_fold(init, &mut f)?;
        self.i2.try_fold(b, f)
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.i2.next_back() {
            Some(t) => Some(t),
            None => {
                mem::swap(&mut self.i1, &mut self.i2);
                self.i2.next_back()
            }
        }
    }

    #[inline]
    fn advance_back_by(&mut self, n: usize) -> Result<(), usize> {
        let m = match self.i2.advance_back_by(n) {
            Ok(_) => return Ok(()),
            Err(m) => m,
        };

        mem::swap(&mut self.i1, &mut self.i2);
        self.i2.advance_back_by(n - m).map_err(|o| m + o)
    }

    #[inline]
    fn rfold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let accum = self.i2.rfold(init, &mut f);
        self.i1.rfold(accum, f)
    }

    #[inline]
    fn rfind<P>(&mut self, mut predicate: P) -> Option<Self::Item>
    where
        Self: Sized,
        P: FnMut(&Self::Item) -> bool,
    {
        self.i2.rfind(&mut predicate).or_else(|| self.i1.rfind(predicate))
    }

    #[inline]
    fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        let b = self.i2.try_rfold(init, &mut f)?;
        self.i1.try_rfold(b, f)
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        self.i1.len() + self.i2.len()
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> {}

unsafe impl<'a, T> TrustedLen for Iter<'a, T> {}

impl<'a, T> Clone for Iter<'a, T> {
    #[inline]
    fn clone(&self) -> Self {
        Self { i1: self.i1.clone(), i2: self.i2.clone() }
    }
}

impl<'a, T: fmt::Debug> fmt::Debug for Iter<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct IterFormatter<'a, 'b, T>(&'b Iter<'a, T>);

        impl<'a, 'b, T: fmt::Debug> fmt::Debug for IterFormatter<'a, 'b, T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_list().entries(self.0.clone()).finish()
            }
        }

        f.debug_tuple("Iter").field(&IterFormatter(self)).finish()
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.i1.next() {
            Some(t) => Some(t),
            None => {
                mem::swap(&mut self.i1, &mut self.i2);
                self.i1.next()
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    #[inline]
    fn advance_by(&mut self, n: usize) -> Result<(), usize> {
        let m = match self.i1.advance_by(n) {
            Ok(_) => return Ok(()),
            Err(m) => m,
        };
        match self.i2.advance_by(n - m) {
            Ok(_) => Ok(()),
            Err(o) => Err(m + o),
        }
    }

    #[inline]
    fn all<F>(&mut self, mut f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        self.i1.all(&mut f) && self.i2.all(f)
    }

    #[inline]
    fn any<F>(&mut self, mut f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        self.i1.any(&mut f) || self.i2.any(f)
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len()
    }

    #[inline]
    fn find<P>(&mut self, mut predicate: P) -> Option<Self::Item>
    where
        Self: Sized,
        P: FnMut(&Self::Item) -> bool,
    {
        self.i1.find(&mut predicate).or_else(|| self.i2.find(predicate))
    }

    #[inline]
    fn find_map<B, F>(&mut self, mut f: F) -> Option<B>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> Option<B>,
    {
        self.i1.find_map(&mut f).or_else(|| self.i2.find_map(f))
    }

    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let accum = self.i1.fold(init, &mut f);
        self.i2.fold(accum, f)
    }

    #[inline]
    fn for_each<F>(self, mut f: F)
    where
        Self: Sized,
        F: FnMut(Self::Item),
    {
        self.i1.for_each(&mut f);
        self.i2.for_each(f);
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    #[inline]
    fn max_by<F>(self, mut compare: F) -> Option<Self::Item>
    where
        Self: Sized,
        F: FnMut(&Self::Item, &Self::Item) -> Ordering,
    {
        let (m1, m2) = match (self.i1.max_by(&mut compare), self.i2.max_by(&mut compare)) {
            (None, None) => return None,
            (None, Some(max)) | (Some(max), None) => return Some(max),
            (Some(m1), Some(m2)) => (m1, m2),
        };
        match compare(&m1, &m2) {
            Ordering::Less => Some(m2),
            _ => Some(m1),
        }
    }

    #[inline]
    fn min_by<F>(self, mut compare: F) -> Option<Self::Item>
    where
        Self: Sized,
        F: FnMut(&Self::Item, &Self::Item) -> Ordering,
    {
        let (m1, m2) = match (self.i1.min_by(&mut compare), self.i2.min_by(&mut compare)) {
            (None, None) => return None,
            (None, Some(min)) | (Some(min), None) => return Some(min),
            (Some(m1), Some(m2)) => (m1, m2),
        };
        match compare(&m1, &m2) {
            Ordering::Greater => Some(m2),
            _ => Some(m1),
        }
    }

    #[inline]
    fn position<P>(&mut self, mut predicate: P) -> Option<usize>
    where
        Self: Sized,
        P: FnMut(Self::Item) -> bool,
    {
        let len1 = self.i1.len();
        if let Some(i) = self.i1.position(&mut predicate) {
            return Some(i);
        }
        mem::swap(&mut self.i1, &mut self.i2);
        self.i1.position(predicate).map(|i| i + len1)
    }

    #[inline]
    fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        let b = self.i1.try_fold(init, &mut f)?;
        self.i2.try_fold(b, f)
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.i2.next_back() {
            Some(t) => Some(t),
            None => {
                mem::swap(&mut self.i1, &mut self.i2);
                self.i2.next_back()
            }
        }
    }

    #[inline]
    fn advance_back_by(&mut self, n: usize) -> Result<(), usize> {
        let m = match self.i2.advance_back_by(n) {
            Ok(_) => return Ok(()),
            Err(m) => m,
        };

        mem::swap(&mut self.i1, &mut self.i2);
        self.i2.advance_back_by(n - m).map_err(|o| m + o)
    }

    #[inline]
    fn rfold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let accum = self.i2.rfold(init, &mut f);
        self.i1.rfold(accum, f)
    }

    #[inline]
    fn rfind<P>(&mut self, mut predicate: P) -> Option<Self::Item>
    where
        Self: Sized,
        P: FnMut(&Self::Item) -> bool,
    {
        self.i2.rfind(&mut predicate).or_else(|| self.i1.rfind(predicate))
    }

    #[inline]
    fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        let b = self.i2.try_rfold(init, &mut f)?;
        self.i1.try_rfold(b, f)
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        self.i1.len() + self.i2.len()
    }
}

impl<'a, T> FusedIterator for IterMut<'a, T> {}

unsafe impl<'a, T> TrustedLen for IterMut<'a, T> {}

impl<'a, T> IterMut<'a, T> {
    #[inline]
    pub fn as_iter(&self) -> Iter<'_, T> {
        Iter { i1: self.i1.as_slice().iter(), i2: self.i2.as_slice().iter() }
    }
}

impl<'a, T: fmt::Debug> fmt::Debug for IterMut<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct IterMutFormatter<'a, 'b, T>(&'b IterMut<'a, T>);

        impl<'a, 'b, T: fmt::Debug> fmt::Debug for IterMutFormatter<'a, 'b, T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_list().entries(self.0.as_iter()).finish()
            }
        }

        f.debug_tuple("Iter").field(&IterMutFormatter(self)).finish()
    }
}

impl<T, A: Allocator> Iterator for IntoIter<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.len, Some(self.0.len))
    }
}

impl<T, A: Allocator> DoubleEndedIterator for IntoIter<T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_back()
    }
}

impl<T, A: Allocator> ExactSizeIterator for IntoIter<T, A> {
    #[inline]
    fn len(&self) -> usize {
        self.0.len
    }
}

impl<T, A: Allocator> FusedIterator for IntoIter<T, A> {}

unsafe impl<T, A: Allocator> TrustedLen for IntoIter<T, A> {}

pub struct Drain<'a, T, A: Allocator> {
    deque: &'a mut Deque<T, A>,
    orig_len: usize,
    drain_start: usize,
    drain_len: usize,
    idx: usize,
    remaining: usize,
}

impl<'a, T, A: Allocator> Iterator for Drain<'a, T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let ptr = unsafe { self.deque.ptr_at_idx(self.idx) };
        self.idx += 1;
        self.remaining -= 1;
        unsafe { Some(ptr::read(ptr)) }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, T, A: Allocator> DoubleEndedIterator for Drain<'a, T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let ptr = unsafe { self.deque.ptr_at_idx(self.idx + self.remaining) };
        unsafe { Some(ptr::read(ptr)) }
    }
}

impl<'a, T, A: Allocator> ExactSizeIterator for Drain<'a, T, A> {
    fn len(&self) -> usize {
        self.remaining
    }
}

impl<'a, T, A: Allocator> FusedIterator for Drain<'a, T, A> {}

unsafe impl<'a, T, A: Allocator> TrustedLen for Drain<'a, T, A> {}

impl<'a, T, A: Allocator> Drop for Drain<'a, T, A> {
    fn drop(&mut self) {
        struct DropGuard<'a, 'b, T, A: Allocator>(&'a mut Drain<'b, T, A>);

        impl<'a, 'b, T, A: Allocator> Drop for DropGuard<'a, 'b, T, A> {
            fn drop(&mut self) {
                for _ in &mut self.0 {}

                let deque = &mut self.0.deque;

                let head_len = self.0.drain_start;
                let tail_len = self.0.orig_len - self.0.drain_start - self.0.drain_len;

                if head_len < tail_len {
                    unsafe { deque.copy_range_internal(0, self.0.drain_len, head_len) };
                    deque.head = deque.wrap_idx(self.0.drain_len);
                } else {
                    unsafe {
                        deque.copy_range_internal(
                            self.0.drain_start + self.0.drain_len,
                            self.0.drain_start,
                            tail_len,
                        )
                    }
                }

                deque.len = self.0.orig_len - self.0.drain_len;
            }
        }

        while let Some(item) = self.next() {
            let guard = DropGuard(self);
            drop(item);
            mem::forget(guard);
        }

        DropGuard(self);
    }
}
