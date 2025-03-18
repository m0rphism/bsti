pub mod dfa;
pub mod dfa_to_regex;
pub mod parser;
pub mod pattern;
pub mod pretty;
pub mod random;
pub mod regex;
pub mod regex_to_dfa;

#[cfg(test)]
mod tests;

#[doc(inline)]
pub use self::dfa::*;
#[doc(inline)]
pub use self::dfa_to_regex::*;
#[doc(inline)]
pub use self::pattern::*;
#[doc(inline)]
pub use self::random::*;
#[doc(inline)]
pub use self::regex::*;
// #[doc(inline)]
// pub use self::regex_to_dfa::*;
