use std::ops::Index;

use bitvec::prelude::BitArray;

#[derive(Debug, Clone)]
pub enum BitVec {
    Stack(bitvec::BitArr!(for 52, in u8), u8),
    Heap(bitvec::vec::BitVec<u8>),
}

impl Default for BitVec {
    fn default() -> Self {
        BitVec::Stack(bitvec::array::BitArray::ZERO, 0u8)
    }
}

impl BitVec {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        if capacity > 52 {
            Self::Heap(bitvec::vec::BitVec::with_capacity(capacity))
        } else {
            Self::Stack(BitArray::ZERO, 0)
        }
    }

    pub fn push(&mut self, bit: bool) {
        match self {
            BitVec::Stack(bitarray, len) => {
                if *len >= 52 {
                    let mut bitvec = bitvec::vec::BitVec::from_slice(bitarray.as_raw_slice());
                    bitvec.push(bit);
                    *self = Self::Heap(bitvec);
                } else {
                    bitarray.set(*len as usize, bit);
                    *len += 1;
                }
            }
            BitVec::Heap(bitvec) => {
                bitvec.push(bit);
            }
        }
    }

    pub fn set(&mut self, index: usize, bit: bool) {
        match self {
            BitVec::Stack(array, len) if index < (*len as usize) => {
                array.set(index, bit);
            }
            BitVec::Heap(bitvec) => {
                bitvec.set(index, bit);
            }
            _ => panic!(),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            BitVec::Stack(_, len) => *len as usize,
            BitVec::Heap(bitvec) => bitvec.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            BitVec::Stack(_, len) => *len == 0,
            BitVec::Heap(bitvec) => bitvec.is_empty(),
        }
    }
}

impl Index<usize> for BitVec {
    type Output = <bitvec::vec::BitVec as Index<usize>>::Output;

    fn index(&self, index: usize) -> &Self::Output {
        match self {
            BitVec::Stack(bitarray, len) if index < (*len as usize) => &bitarray[index],
            BitVec::Heap(vec) => &vec[index],
            _ => panic!(),
        }
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn bitvec_layout() {
        assert_eq!(
            std::mem::size_of::<super::BitVec>(),
            std::mem::size_of::<bitvec::vec::BitVec<usize>>()
        )
    }
}
