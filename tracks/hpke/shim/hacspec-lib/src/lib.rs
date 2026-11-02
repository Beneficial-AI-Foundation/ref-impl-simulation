//! Plain-Rust stand-in for the subset of `hacspec_lib` used by hpke-spec.
//! Secret integers are public machine integers. `Seq<T>` wraps a `Vec<T>`.
//! No traits beyond `Clone`, `Index`, `IndexMut`, `BitXor`, so that
//! Charon/Aeneas accept it.
#![allow(non_snake_case)]
extern crate alloc;
pub use alloc::vec::Vec;
pub use core::ops::{BitXor, Index, IndexMut};

pub type U8 = u8;
pub type U16 = u16;
pub type U32 = u32;
pub fn U8(x: u8) -> u8 {
    x
}
pub fn U16(x: u16) -> u16 {
    x
}
pub fn U32(x: u32) -> u32 {
    x
}

#[derive(Clone, PartialEq, Debug, Default)]
pub struct Seq<T> {
    pub b: Vec<T>,
}

pub type ByteSeq = Seq<u8>;

impl<T: Clone> Seq<T> {
    pub fn from_vec(b: Vec<T>) -> Seq<T> {
        Seq { b }
    }
    pub fn len(&self) -> usize {
        self.b.len()
    }
    pub fn from_seq(s: &Seq<T>) -> Seq<T> {
        s.clone()
    }
    pub fn concat(&self, next: &Seq<T>) -> Seq<T> {
        let mut out = self.b.clone();
        out.extend_from_slice(&next.b);
        Seq { b: out }
    }
    pub fn concat_owned(self, next: Seq<T>) -> Seq<T> {
        let mut out = self.b;
        out.extend_from_slice(&next.b);
        Seq { b: out }
    }
    pub fn into_slice(self, start: usize, len: usize) -> Seq<T> {
        Seq { b: self.b[start..start + len].to_vec() }
    }
}

impl<T: Clone + Default> Seq<T> {
    pub fn new(len: usize) -> Seq<T> {
        Seq { b: alloc::vec![T::default(); len] }
    }
}

impl<T: Copy> Seq<T> {
    pub fn update_slice(mut self, start_out: usize, v: &Seq<T>, start_in: usize, len: usize) -> Seq<T> {
        self.b[start_out..start_out + len].copy_from_slice(&v.b[start_in..start_in + len]);
        self
    }
}

impl<T> Index<usize> for Seq<T> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        &self.b[i]
    }
}

impl<T> IndexMut<usize> for Seq<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        &mut self.b[i]
    }
}

impl BitXor for Seq<u8> {
    type Output = Seq<u8>;
    fn bitxor(self, rhs: Seq<u8>) -> Seq<u8> {
        let mut out = self;
        let mut i = 0;
        while i < out.b.len() {
            out.b[i] = out.b[i] ^ rhs.b[i];
            i += 1;
        }
        out
    }
}

pub fn U16_to_be_bytes(x: u16) -> Seq<u8> {
    let mut b = Vec::new();
    b.push((x >> 8) as u8);
    b.push(x as u8);
    Seq { b }
}

pub fn U32_to_be_bytes(x: u32) -> Seq<u8> {
    let mut b = Vec::new();
    b.push((x >> 24) as u8);
    b.push((x >> 16) as u8);
    b.push((x >> 8) as u8);
    b.push(x as u8);
    Seq { b }
}

#[macro_export]
macro_rules! byte_seq {
    ($($x:expr),* $(,)?) => {
        $crate::Seq::<u8>::from_vec($crate::byte_vec(&[$($x),*]))
    };
}

pub fn byte_vec(xs: &[u8]) -> Vec<u8> {
    xs.to_vec()
}
