use std::sync::{
    atomic::{AtomicUsize, Ordering},
    OnceLock,
};

pub static DEPTH: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug)]
pub struct Config {
    pub enabled: bool,
    pub print_full_paths: bool,
}

impl Config {
    fn from_env() -> Self {
        Self {
            enabled: std::env::var("KW_LOG").is_ok_and(|s| s == "1"),
            print_full_paths: std::env::var("KW_FULL_PATHS").is_ok_and(|s| s == "1"),
        }
    }
}

pub static CONFIG: OnceLock<Config> = OnceLock::new();

pub fn get_depth() -> usize {
    DEPTH.load(Ordering::Relaxed)
}

pub fn get_config() -> &'static Config {
    CONFIG.get_or_init(|| Config::from_env())
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
        $crate::logn!($($arg)*);
        println!();
    };
}

#[macro_export]
macro_rules! logn {
    ($($arg:tt)*) => {
        if $crate::log::get_config().enabled {
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
