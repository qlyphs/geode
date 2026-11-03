//! A counting global allocator over jemalloc: exact live and peak heap bytes, independent of how the OS
//! accounts freed or compressed pages.
//!
//! Round 10 adds SSD-backed storage for large arrays. With `H9_SPILL_DIR` set, every allocation of
//! at least `H9_SPILL_MIN` bytes (default 256 MiB) is a shared mapping of a fresh, already unlinked
//! file in that directory instead of anonymous memory. The program sees the same bytes: only where
//! the pages live changes. Under a memory limit the kernel writes such pages back to the file and
//! drops them from RAM, so resident memory is bounded by the limit while the arrays stay intact.
//! Spilled bytes are counted in the live heap as before, and separately (`spill()`).

use std::alloc::{GlobalAlloc, Layout};
use tikv_jemallocator::Jemalloc;

const JE: Jemalloc = Jemalloc;

/// Return freed pages to the OS at once, so the process footprint follows the live heap.
#[allow(non_upper_case_globals)]
#[unsafe(export_name = "_rjem_malloc_conf")]
pub static malloc_conf: &u8 = &b"dirty_decay_ms:0,muzzy_decay_ms:0\0"[0];
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

pub struct Counting;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static SPILL_LIVE: AtomicUsize = AtomicUsize::new(0);
static SPILL_PEAK: AtomicUsize = AtomicUsize::new(0);
static SPILL_COUNT: AtomicUsize = AtomicUsize::new(0);

/// 0 = not read yet, 1 = off, 2 = on.
static SPILL_STATE: AtomicU8 = AtomicU8::new(0);
static SPILL_MIN: AtomicUsize = AtomicUsize::new(256 << 20);
/// NUL-terminated directory path (read once from the environment).
static mut SPILL_DIR: [u8; 256] = [0; 256];
static SPILL_SEQ: AtomicUsize = AtomicUsize::new(0);

/// Addresses of live spilled mappings (0 = free slot). Large arrays are few, so a linear scan on
/// the large-size path is cheap, and no allocation happens inside the allocator.
const SLOTS: usize = 4096;
static MAPS: [AtomicUsize; SLOTS] = [const { AtomicUsize::new(0) }; SLOTS];

fn getenv(name: &[u8]) -> Option<&'static [u8]> {
    // libc getenv does not allocate; the returned string lives in the environment block.
    let p = unsafe { libc::getenv(name.as_ptr() as *const libc::c_char) };
    if p.is_null() {
        return None;
    }
    let len = unsafe { libc::strlen(p) };
    Some(unsafe { std::slice::from_raw_parts(p as *const u8, len) })
}

fn spill_on() -> bool {
    match SPILL_STATE.load(Ordering::Acquire) {
        1 => false,
        2 => true,
        _ => {
            let on = match getenv(b"H9_SPILL_DIR\0") {
                Some(d) if !d.is_empty() && d.len() < 200 => {
                    unsafe {
                        let dst: &mut [u8; 256] = &mut *(&raw mut SPILL_DIR);
                        dst[..d.len()].copy_from_slice(d);
                        dst[d.len()] = 0;
                    }
                    if let Some(m) = getenv(b"H9_SPILL_MIN\0") {
                        let v = m.iter().try_fold(0usize, |a, &c| if c.is_ascii_digit() { Some(a * 10 + (c - b'0') as usize) } else { None });
                        if let Some(v) = v {
                            SPILL_MIN.store(v.max(4096), Ordering::Relaxed);
                        }
                    }
                    true
                }
                _ => false,
            };
            SPILL_STATE.store(if on { 2 } else { 1 }, Ordering::Release);
            on
        }
    }
}

/// Decimal digits of v appended at path[k..]; returns the new end.
fn put_num(path: &mut [u8; 256], mut k: usize, v: usize) -> usize {
    let mut digits = [0u8; 20];
    let (mut n, mut nd) = (v, 0);
    loop {
        digits[nd] = b'0' + (n % 10) as u8;
        nd += 1;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    for i in (0..nd).rev() {
        path[k] = digits[i];
        k += 1;
    }
    k
}

/// A shared mapping of a new unlinked file of `size` bytes (zero-filled), or null.
unsafe fn spill_map(size: usize) -> *mut u8 {
    let seq = SPILL_SEQ.fetch_add(1, Ordering::Relaxed);
    let mut path = [0u8; 256];
    let dir = unsafe { &*(&raw const SPILL_DIR) };
    let dl = dir.iter().position(|&c| c == 0).unwrap_or(0);
    path[..dl].copy_from_slice(&dir[..dl]);
    let mut k = dl;
    for &c in b"/r3-spill-" {
        path[k] = c;
        k += 1;
    }
    k = put_num(&mut path, k, std::process::id() as usize);
    path[k] = b'-';
    k = put_num(&mut path, k + 1, seq);
    path[k] = 0;
    let fd = unsafe { libc::open(path.as_ptr() as *const libc::c_char, libc::O_RDWR | libc::O_CREAT | libc::O_EXCL, 0o600) };
    if fd < 0 {
        return core::ptr::null_mut();
    }
    unsafe { libc::unlink(path.as_ptr() as *const libc::c_char) };
    let len = size.div_ceil(4096) * 4096;
    if unsafe { libc::ftruncate(fd, len as libc::off_t) } != 0 {
        unsafe { libc::close(fd) };
        return core::ptr::null_mut();
    }
    let p = unsafe { libc::mmap(core::ptr::null_mut(), len, libc::PROT_READ | libc::PROT_WRITE, libc::MAP_SHARED, fd, 0) };
    unsafe { libc::close(fd) };
    if p == libc::MAP_FAILED {
        return core::ptr::null_mut();
    }
    let a = p as usize;
    for s in MAPS.iter() {
        if s.compare_exchange(0, a, Ordering::AcqRel, Ordering::Relaxed).is_ok() {
            let now = SPILL_LIVE.fetch_add(len, Ordering::Relaxed) + len;
            SPILL_PEAK.fetch_max(now, Ordering::Relaxed);
            SPILL_COUNT.fetch_add(1, Ordering::Relaxed);
            return p as *mut u8;
        }
    }
    // Registry full: give the mapping back and use ordinary memory.
    unsafe { libc::munmap(p, len) };
    core::ptr::null_mut()
}

fn is_spilled(p: *mut u8) -> bool {
    let a = p as usize;
    MAPS.iter().any(|s| s.load(Ordering::Acquire) == a)
}

/// Unmap `p` if it is a spilled mapping; returns whether it was.
unsafe fn spill_unmap(p: *mut u8, size: usize) -> bool {
    let a = p as usize;
    for s in MAPS.iter() {
        if s.load(Ordering::Acquire) == a && s.compare_exchange(a, 0, Ordering::AcqRel, Ordering::Relaxed).is_ok() {
            let len = size.div_ceil(4096) * 4096;
            unsafe { libc::munmap(p as *mut libc::c_void, len) };
            SPILL_LIVE.fetch_sub(len, Ordering::Relaxed);
            return true;
        }
    }
    false
}

#[inline]
fn big(l: &Layout) -> bool {
    l.size() >= SPILL_MIN.load(Ordering::Relaxed) && l.align() <= 4096 && spill_on()
}

/// Only allocations made by `spill_map` can be spilled; they are page aligned and at least a page.
#[inline]
fn maybe_spilled(p: *mut u8, size: usize) -> bool {
    size >= 4096 && (p as usize) % 4096 == 0 && SPILL_STATE.load(Ordering::Relaxed) == 2
}

#[inline]
fn count_add(n: usize) {
    let now = LIVE.fetch_add(n, Ordering::Relaxed) + n;
    PEAK.fetch_max(now, Ordering::Relaxed);
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let mut p = core::ptr::null_mut();
        if big(&l) {
            p = unsafe { spill_map(l.size()) };
        }
        if p.is_null() {
            p = unsafe { JE.alloc(l) };
        }
        if !p.is_null() {
            count_add(l.size());
        }
        p
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        let mut p = core::ptr::null_mut();
        if big(&l) {
            // A new file reads as zeros.
            p = unsafe { spill_map(l.size()) };
        }
        if p.is_null() {
            p = unsafe { JE.alloc_zeroed(l) };
        }
        if !p.is_null() {
            count_add(l.size());
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        let spilled = maybe_spilled(p, l.size()) && unsafe { spill_unmap(p, l.size()) };
        if !spilled {
            unsafe { JE.dealloc(p, l) };
        }
        LIVE.fetch_sub(l.size(), Ordering::Relaxed);
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        let was_spilled = maybe_spilled(p, l.size()) && is_spilled(p);
        let nl = unsafe { Layout::from_size_align_unchecked(new, l.align()) };
        if was_spilled || big(&nl) {
            // Move between storages (or grow a mapping) by copy.
            let q = unsafe { self.alloc(nl) };
            if !q.is_null() {
                unsafe { core::ptr::copy_nonoverlapping(p, q, l.size().min(new)) };
                unsafe { self.dealloc(p, l) };
            }
            return q;
        }
        let q = unsafe { JE.realloc(p, l, new) };
        if !q.is_null() {
            if new >= l.size() {
                count_add(new - l.size());
            } else {
                LIVE.fetch_sub(l.size() - new, Ordering::Relaxed);
            }
        }
        q
    }
}

/// (live, peak since the last reset) heap bytes, spilled arrays included.
pub fn heap() -> (usize, usize) {
    (LIVE.load(Ordering::Relaxed), PEAK.load(Ordering::Relaxed))
}

pub fn reset_peak() {
    PEAK.store(LIVE.load(Ordering::Relaxed), Ordering::Relaxed);
}

/// (live, lifetime peak, number of mappings made) of the SSD-backed arrays, in bytes.
pub fn spill() -> (usize, usize, usize) {
    (SPILL_LIVE.load(Ordering::Relaxed), SPILL_PEAK.load(Ordering::Relaxed), SPILL_COUNT.load(Ordering::Relaxed))
}

/// One line describing the storage mode.
pub fn describe() -> String {
    if spill_on() {
        let dir = unsafe { &*(&raw const SPILL_DIR) };
        let dl = dir.iter().position(|&c| c == 0).unwrap_or(0);
        format!("SSD-backed arrays on: allocations >= {} KiB are shared mappings of unlinked files in {}", SPILL_MIN.load(Ordering::Relaxed) >> 10, String::from_utf8_lossy(&dir[..dl]))
    } else {
        "SSD-backed arrays off (all arrays in anonymous memory)".into()
    }
}
