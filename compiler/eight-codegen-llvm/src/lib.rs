use eight_middle::mir::function::MirFunction;
use eight_middle::mir::module::MirModule;
use eight_middle::mir::ty::MirType;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicMetadataTypeEnum, BasicType};
use inkwell::AddressSpace;

pub struct LLVMCodeGeneratorContext {
    llvm_context: Context,
}

impl LLVMCodeGeneratorContext {
    pub fn new() -> Self {
        Self {
            llvm_context: Context::create(),
        }
    }
}

impl Default for LLVMCodeGeneratorContext {
    fn default() -> Self {
        Self::new()
    }
}

/// A pass that generates LLVM IR from the MIR.
pub struct MirModuleLLVMCodeGeneratorPass<'l> {
    context: &'l Context,
    module: Module<'l>,
}

impl<'l, 'mir> MirModuleLLVMCodeGeneratorPass<'l> {
    pub fn new(ctx: &'l LLVMCodeGeneratorContext) -> Self {
        Self {
            module: ctx.llvm_context.create_module("eightc"),
            context: &ctx.llvm_context,
        }
    }

    pub fn visit_module(&mut self, node: &'mir MirModule<'mir>) {
        for function in node.data().functions() {
            if function.is_external() {
                self.visit_extern_function(function);
            }
        }
    }

    pub fn visit_extern_function(&mut self, node: &'mir MirFunction<'mir>) {
        let arguments = node
            .ty()
            .parameters
            .iter()
            .map(|ty| self.visit_type(ty))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        // TODO: Can this be made prettier and not overlap with `visit_type`? Inkwell does not
        //   enumerate void into `BasicMetadataTypeEnum`. so we have to do this.
        let signature_ty = match node.ty().return_type {
            MirType::Void(_) => self.context.void_type().fn_type(&arguments, false),
            MirType::Bool(_) => self.context.bool_type().fn_type(&arguments, false),
            MirType::Integer32(_) => self.context.i32_type().fn_type(&arguments, false),
            MirType::Pointer(_) => self
                .context
                .ptr_type(AddressSpace::default())
                .fn_type(&arguments, false),
            MirType::Function(_) => unimplemented!("cannot lower this type"),
        };
        self.module
            .add_function(node.name(), signature_ty, Some(Linkage::External));
    }

    pub fn finish(self) {
        self.module.print_to_stderr();
    }

    /// Translate a MIR type into an LLVM type.
    pub fn visit_type(&mut self, node: &'mir MirType<'mir>) -> BasicMetadataTypeEnum<'l> {
        match node {
            MirType::Integer32(_) => self.context.i32_type().into(),
            MirType::Bool(_) => self.context.bool_type().into(),
            MirType::Pointer(_) => self.context.ptr_type(AddressSpace::default()).into(),
            MirType::Function(_) | MirType::Void(_) => unimplemented!("cannot lower this type"),
        }
    }
}
