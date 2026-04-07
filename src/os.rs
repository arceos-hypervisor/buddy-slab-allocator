use spin::RwLock;

pub trait Os: Sync {
    fn current_cpu_idx(&self) -> usize;
}

pub struct NoImplOs;

impl Os for NoImplOs {
    fn current_cpu_idx(&self) -> usize {
        panic!("buddy-slab-allocator: Os provider is not initialized")
    }
}

static NO_IMPL_OS: NoImplOs = NoImplOs;
static OS_PROVIDER: RwLock<&'static dyn Os> = RwLock::new(&NO_IMPL_OS);

pub(crate) fn set_os_provider(os: &'static dyn Os) {
    *OS_PROVIDER.write() = os;
}

pub fn current_cpu_idx() -> usize {
    OS_PROVIDER.read().current_cpu_idx()
}
