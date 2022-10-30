use std::{
    cell::{Ref, RefCell},
    rc::Rc,
};

use crate::common::HashMap;
use crate::common::HashSet;

use crate::diagnostics::DiagnosticContext;

#[derive(Copy, Clone)]
pub enum OutputType {
    Library,
    Executable,
}

struct GlobalCtxInner {
    pub diag: DiagnosticContext,
    pub cfg: HashMap<String, Option<String>>,
    pub options: HashSet<String>,
    pub output_type: OutputType,
}

#[derive(Clone)]
pub struct GlobalCtx {
    inner: Rc<RefCell<GlobalCtxInner>>,
}

impl GlobalCtx {
    pub fn new(output_type: OutputType, options: Vec<String>) -> Self {
        let mut result = Self {
            inner: Rc::new(RefCell::new(GlobalCtxInner {
                diag: DiagnosticContext::new(),
                cfg: HashMap::default(),
                options: options.into_iter().collect(),
                output_type,
            })),
        };

        // We are the alumina-boot compiler
        result.add_flag("boot");

        // No cross-compilation, so we just use whatever the compiler was compiled with
        result.add_cfg("target_os", std::env::consts::OS);
        result.add_cfg("target_family", std::env::consts::FAMILY);
        result.add_cfg("target_arch", std::env::consts::ARCH);
        result.add_cfg(
            "target_pointer_width",
            (std::mem::size_of::<usize>() * 8).to_string(),
        );

        #[cfg(target_endian = "big")]
        result.add_cfg("target_endian", "big".to_string());
        #[cfg(target_endian = "little")]
        result.add_cfg("target_endian", "little".to_string());

        match output_type {
            OutputType::Executable => {
                result.add_cfg("output_type", "executable");
            }
            OutputType::Library => {
                result.add_cfg("output_type", "library");
            }
        };

        result
    }

    pub fn should_generate_main_glue(&self) -> bool {
        matches!(self.inner.borrow().output_type, OutputType::Executable)
    }

    pub fn has_option(&self, name: &str) -> bool {
        self.inner.borrow().options.contains(name)
    }

    pub fn diag(&self) -> Ref<'_, DiagnosticContext> {
        Ref::map(self.inner.borrow(), |inner| &inner.diag)
    }

    pub fn add_flag(&mut self, value: impl ToString) {
        let mut borrowed = self.inner.borrow_mut();
        borrowed.cfg.insert(value.to_string(), None);
    }

    pub fn has_flag(&self, name: &str) -> bool {
        self.inner.borrow().cfg.contains_key(name)
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
