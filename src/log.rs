use std::sync::atomic::{AtomicUsize, Ordering};

pub static DEPTH: AtomicUsize = AtomicUsize::new(0);

pub fn get_depth() -> usize {
    DEPTH.load(Ordering::SeqCst)
}

pub struct DepthGuard;

impl Drop for DepthGuard {
    fn drop(&mut self) {
        DEPTH.fetch_sub(1, Ordering::SeqCst);
    }
}

pub fn enter() -> DepthGuard {
    DEPTH.fetch_add(1, Ordering::SeqCst);
    DepthGuard
}

#[macro_export]
macro_rules! log {
    ($($arg:tt)*) => {
        if option_env!("KW_LOG").is_some() {
            $crate::logn!($($arg)*);
            println!();
        }
    };
}

#[macro_export]
macro_rules! logn {
    ($($arg:tt)*) => {
        if option_env!("KW_LOG").is_some() {
            let depth = $crate::log::get_depth();
            let mut bars = String::with_capacity(depth);
            for _ in 0..depth {
                bars.push('|');
            }
            print!("{}", ::crossterm::style::Stylize::dim(::crossterm::style::Stylize::dark_grey(bars)));
            print!($($arg)*);
        }
    };
}
