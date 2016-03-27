#[derive(Debug, Clone, PartialEq, Eq, Hash, RustcEncodable, RustcDecodable)]
pub struct LWWReg<T, A: Ord> {
    pub value: T,
    pub dot: A,
}

impl<T, A: Ord> LWWReg<T, A> {
    pub fn merge(&mut self, other: LWWReg<T, A>) {
        if other.dot > self.dot {
            self.value = other.value;
            self.dot = other.dot;
        }
    }
}
