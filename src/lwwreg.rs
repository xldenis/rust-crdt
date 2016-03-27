use bincode::SizeLimit;
use bincode::rustc_serialize::{encode, decode, DecodingResult};
use rustc_serialize::{Encodable, Decodable};

#[derive(Debug, Clone, PartialEq, Eq, Hash, RustcEncodable, RustcDecodable)]
pub struct LWWReg<T: Encodable + Decodable, A: Ord + Encodable + Decodable> {
    pub value: T,
    pub dot: A,
}

impl<T: Encodable + Decodable, A: Ord + Encodable + Decodable> LWWReg<T, A> {
    pub fn to_binary(&self) -> Vec<u8> {
        encode(&self, SizeLimit::Infinite).unwrap()
    }

    pub fn from_binary(encoded: Vec<u8>) -> DecodingResult<Self> {
        decode(&encoded[..])
    }

    pub fn merge(&mut self, other: LWWReg<T, A>) {
        if other.dot > self.dot {
            self.value = other.value;
            self.dot = other.dot;
        }
    }
}
