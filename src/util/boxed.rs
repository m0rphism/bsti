pub trait Boxed<T> {
    fn boxed(self) -> Box<T>;
}

impl<T> Boxed<T> for T {
    fn boxed(self) -> Box<T> {
        Box::new(self)
    }
}

impl<'a, T: Clone> Boxed<T> for &'a T {
    fn boxed(self) -> Box<T> {
        Box::new(self.clone())
    }
}

impl<T> Boxed<T> for Box<T> {
    fn boxed(self) -> Box<T> {
        self
    }
}

impl<'a, T: Clone> Boxed<T> for &'a Box<T> {
    fn boxed(self) -> Box<T> {
        self.clone()
    }
}
