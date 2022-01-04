use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    rc::Rc,
};

use crate::diagnostics::DiagnosticContext;

struct GlobalCtxInner {
    pub diag: DiagnosticContext,
    pub cfg: HashMap<String, Option<String>>,
}

#[derive(Clone)]
pub struct GlobalCtx {
    inner: Rc<RefCell<GlobalCtxInner>>,
}

impl GlobalCtx {
    pub fn new() -> Self {
        let mut result = Self {
            inner: Rc::new(RefCell::new(GlobalCtxInner {
                diag: DiagnosticContext::new(),
                cfg: HashMap::new(),
            })),
        };

        // No cross-compilation, so we just use whatever the compiler was compiled with
        result.add_cfg("target_os", std::env::consts::OS);
        result.add_cfg("target_family", std::env::consts::FAMILY);
        result.add_cfg("target_arch", std::env::consts::ARCH);
        result.add_cfg(
            "target_pointer_width",
            (std::mem::size_of::<usize>() * 8).to_string(),
        );

        result
    }

    pub fn diag(&self) -> Ref<'_, DiagnosticContext> {
        Ref::map(self.inner.borrow(), |inner| &inner.diag)
    }

    pub fn add_flag(&mut self, value: impl ToString) {
        let mut borrowed = self.inner.borrow_mut();
        borrowed.cfg.insert(value.to_string(), None);
    }

    pub fn add_cfg(&mut self, value: impl ToString, value_str: impl ToString) {
        let mut borrowed = self.inner.borrow_mut();
        borrowed
            .cfg
            .insert(value.to_string(), Some(value_str.to_string()));
    }

    pub fn cfg(&self, key: impl ToString) -> Option<Option<String>> {
        let borrowed = self.inner.borrow();
        borrowed.cfg.get(&key.to_string()).cloned()
    }
}
