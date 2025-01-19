pub mod error;

use crate::error::LLVMBackendResult;
use eight_diagnostics::ice;
use eight_middle::mir::bb::{MirBasicBlock, MirBasicBlockId};
use eight_middle::mir::function::{MirFunction, MirFunctionData};
use eight_middle::mir::instruction::{
    MirAllocaInstruction, MirCallInstruction, MirInstruction, MirInstructionId, MirLoadInstruction,
    MirStoreInstruction,
};
use eight_middle::mir::module::{MirModule, MirModuleData};
use eight_middle::mir::ty::{MirFunctionType, MirType};
use eight_middle::mir::value::{MirConstantBool, MirConstantInteger32, MirValue, MirValueId};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum, FunctionType};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, InstructionValue};
use inkwell::AddressSpace;
use std::collections::BTreeMap;

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
    builder: Builder<'l>,

    basic_block_cache: BTreeMap<MirBasicBlockId, BasicBlock<'l>>,
    basic_value_cache: BTreeMap<MirValueId, BasicValueEnum<'l>>,
    instruction_cache: BTreeMap<MirInstructionId, InstructionValue<'l>>,
}

impl<'l, 'mir> MirModuleLLVMCodeGeneratorPass<'l> {
    pub fn new(ctx: &'l LLVMCodeGeneratorContext) -> Self {
        Self {
            module: ctx.llvm_context.create_module("eightc"),
            builder: ctx.llvm_context.create_builder(),
            context: &ctx.llvm_context,

            basic_block_cache: BTreeMap::new(),
            basic_value_cache: BTreeMap::new(),
            instruction_cache: BTreeMap::new(),
        }
    }

    pub fn visit_module(&mut self, node: &'mir MirModule<'mir>) -> LLVMBackendResult<()> {
        for f in node.data().functions() {
            self.forward_declare_function(f)?;
        }

        for function in node.data().functions() {
            let f = self
                .module
                .get_function(function.name())
                .unwrap_or_else(|| ice!("function disappeared right after forward declaration"));
            if function.is_external() {
                continue;
            }
            self.visit_function(node.data(), f, function)?;
        }
        Ok(())
    }

    /// Register the function to the LLVM module
    pub fn forward_declare_function(
        &mut self,
        node: &'mir MirFunction<'mir>,
    ) -> LLVMBackendResult<()> {
        let signature_ty = self.visit_function_type(node.ty());
        let fun = self
            .module
            .add_function(node.name(), signature_ty, Some(Linkage::External));
        fun.set_call_conventions(0);
        Ok(())
    }

    pub fn visit_function(
        &mut self,
        gcx: &'mir MirModuleData,
        function: FunctionValue<'l>,
        node: &'mir MirFunction<'mir>,
    ) -> LLVMBackendResult<()> {
        // Ensure all constant values are lowered into LLVM values
        for value in node.data().values() {
            match value {
                MirValue::ConstantInteger32(v) => {
                    self.visit_constant_integer_value(node.data(), function, v)?
                }
                MirValue::ConstantBool(v) => {
                    self.visit_constant_bool_value(node.data(), function, v)?
                }
                _ => continue,
            }
        }

        for bb in node.data().blocks() {
            self.visit_basic_block(gcx, node.data(), function, bb)?;
        }

        // HACK: we dont lower return just yet...
        let zero = self.context.i32_type().const_int(0, false);
        let _ = self.builder.build_return(Some(&zero));
        Ok(())
    }

    pub fn visit_basic_block(
        &mut self,
        gcx: &'mir MirModuleData,
        fcx: &'mir MirFunctionData,
        function: FunctionValue<'l>,
        node: &'mir MirBasicBlock<'mir>,
    ) -> LLVMBackendResult<()> {
        let bb = self.context.append_basic_block(function, node.name);
        self.builder.position_at_end(bb);
        for inst in node.instructions.iter() {
            self.visit_instruction(gcx, fcx, function, fcx.get_instruction(*inst))?;
        }
        Ok(())
    }

    pub fn visit_constant_integer_value(
        &mut self,
        _: &'mir MirFunctionData,
        _: FunctionValue<'l>,
        node: &'mir MirConstantInteger32<'mir>,
    ) -> LLVMBackendResult<()> {
        let value = self.context.i32_type().const_int(node.value as u64, false);
        self.basic_value_cache
            .insert(node.value_id, value.as_basic_value_enum());
        Ok(())
    }

    pub fn visit_constant_bool_value(
        &mut self,
        _: &'mir MirFunctionData,
        _: FunctionValue<'l>,
        node: &'mir MirConstantBool<'mir>,
    ) -> LLVMBackendResult<()> {
        let value = self.context.bool_type().const_int(node.value as u64, false);
        self.basic_value_cache
            .insert(node.value_id, value.as_basic_value_enum());
        Ok(())
    }

    pub fn visit_instruction(
        &mut self,
        mcx: &'mir MirModuleData,
        fcx: &'mir MirFunctionData,
        function: FunctionValue<'l>,
        node: &'mir MirInstruction<'mir>,
    ) -> LLVMBackendResult<()> {
        match node {
            MirInstruction::Alloca(i) => self.visit_alloca_instruction(mcx, fcx, function, i)?,
            MirInstruction::Store(i) => self.visit_store_instruction(mcx, fcx, function, i)?,
            MirInstruction::Call(i) => self.visit_call_instruction(mcx, fcx, function, i)?,
            MirInstruction::Load(i) => self.visit_load_instruction(mcx, fcx, function, i)?,
            MirInstruction::Add(_)
            | MirInstruction::Sub(_)
            | MirInstruction::Mul(_)
            | MirInstruction::Div(_) => {
                unimplemented!("cannot lower this instruction")
            }
        };
        Ok(())
    }

    pub fn visit_alloca_instruction(
        &mut self,
        _: &'mir MirModuleData,
        _: &'mir MirFunctionData,
        _: FunctionValue<'l>,
        node: &'mir MirAllocaInstruction<'mir>,
    ) -> LLVMBackendResult<()> {
        let ty = self.visit_type(node.alloc_ty);
        let inst = self.builder.build_alloca(ty, node.name)?;
        self.instruction_cache.insert(
            node.inst_id,
            inst.as_instruction().expect("alloca is an instruction"),
        );
        self.basic_value_cache
            .insert(node.value_id, inst.as_basic_value_enum());
        Ok(())
    }

    pub fn visit_store_instruction(
        &mut self,
        _: &'mir MirModuleData,
        _: &'mir MirFunctionData,
        _: FunctionValue<'l>,
        node: &'mir MirStoreInstruction<'mir>,
    ) -> LLVMBackendResult<()> {
        let value = self
            .basic_value_cache
            .get(&node.value)
            .expect("value not found");
        let dest = self
            .basic_value_cache
            .get(&node.dest)
            .expect("dest not found");
        let inst = self
            .builder
            .build_store(dest.into_pointer_value(), value.as_basic_value_enum())?;
        self.instruction_cache.insert(node.inst_id, inst);
        Ok(())
    }

    pub fn visit_call_instruction(
        &mut self,
        mcx: &'mir MirModuleData,
        fcx: &'mir MirFunctionData,
        function: FunctionValue<'l>,
        node: &'mir MirCallInstruction<'mir>,
    ) -> LLVMBackendResult<()> {
        let MirValue::Function(id) = fcx.get_value(node.callee) else {
            ice!("callee is not a function");
        };
        let function_name = mcx
            .get_function_name(*id)
            .expect("didnt find function name");
        let callee = self
            .module
            .get_function(function_name)
            .expect("function not found");
        let arguments = node
            .arguments
            .iter()
            .map(|a| {
                self.basic_value_cache
                    .get(a)
                    .expect("argument not found")
                    .as_basic_value_enum()
                    .into()
            })
            .collect::<Vec<_>>();
        // TODO: Can we safely do something about this return value..?
        let _ = self
            .builder
            .build_direct_call(callee, arguments.as_slice(), node.name)?;
        Ok(())
    }

    pub fn visit_load_instruction(
        &mut self,
        _: &'mir MirModuleData,
        _: &'mir MirFunctionData,
        _: FunctionValue<'l>,
        node: &'mir MirLoadInstruction<'mir>,
    ) -> LLVMBackendResult<()> {
        let dest_ty = self.visit_type(node.ty);
        let inst = self.builder.build_load(
            dest_ty,
            self.basic_value_cache
                .get(&node.src)
                .unwrap()
                .into_pointer_value(),
            node.name,
        )?;
        self.basic_value_cache
            .insert(node.value_id, inst.as_basic_value_enum());
        Ok(())
    }

    pub fn finish(self) {
        self.module.print_to_stderr();
    }

    pub fn visit_function_type(&mut self, node: &'mir MirFunctionType<'mir>) -> FunctionType<'l> {
        let arguments = node
            .parameters
            .iter()
            .map(|ty| self.visit_type(ty).into())
            .collect::<Vec<_>>()
            .into_boxed_slice();
        match node.return_type {
            MirType::Void(_) => self.context.void_type().fn_type(&arguments, false),
            _ => self.visit_type(node.return_type).fn_type(&arguments, false),
        }
    }

    /// Translate a MIR type into an LLVM type.
    pub fn visit_type(&mut self, node: &'mir MirType<'mir>) -> BasicTypeEnum<'l> {
        match node {
            MirType::Integer32(_) => self.context.i32_type().into(),
            MirType::Bool(_) => self.context.bool_type().into(),
            MirType::Pointer(_) => self.context.ptr_type(AddressSpace::default()).into(),
            MirType::Function(_) | MirType::Void(_) => unimplemented!("cannot lower this type"),
        }
    }
}
