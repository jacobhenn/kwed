use std::sync::{
    atomic::{AtomicUsize, Ordering},
    OnceLock,
};

pub static DEPTH: AtomicUsize = AtomicUsize::new(0);

pub static ENABLED: OnceLock<bool> = OnceLock::new();

pub fn get_depth() -> usize {
    DEPTH.load(Ordering::Relaxed)
}

pub fn is_enabled() -> bool {
    *ENABLED.get_or_init(|| std::env::var("KW_LOG").is_ok_and(|s| s == "1"))
}

pub struct DepthGuard;

impl Drop for DepthGuard {
    fn drop(&mut self) {
        DEPTH.fetch_sub(1, Ordering::Relaxed);
    }
}

pub fn enter() -> DepthGuard {
    DEPTH.fetch_add(1, Ordering::Relaxed);
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
        if $crate::log::is_enabled() {
            let depth = $crate::log::get_depth();
            let mut bars = String::with_capacity(depth);
            for _ in 0..depth {
                bars.push('|');
            }
            print!("{}", ::yansi::Paint::dim(&::yansi::Paint::black(&bars)));
            print!($($arg)*);
        }
    };
}
