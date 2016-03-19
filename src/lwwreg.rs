pub struct LWWReg<T> {
    value: T,
    dot: u64,
}

impl<T> LWWReg<T> {
    pub fn new(t: T) -> LWWReg<T> {
        LWWReg {
            value: t,
            dot: 0,
        }
    }

}
