use crate::bb::MirBasicBlock;
use crate::function::{MirFunction, MirFunctionData, MirFunctionId};
use crate::instruction::{
    MirAllocaInstruction, MirCallInstruction, MirInstruction, MirInstructionId, MirLoadInstruction,
    MirStoreInstruction,
};
use crate::module::{MirModule, MirModuleData};
use crate::ty::MirType;
use crate::value::{MirConstantBool, MirConstantInteger32, MirValue};
use eight_diagnostics::ice;
use pretty::{Arena, DocAllocator, DocBuilder};

#[derive(Default)]
pub struct MirModuleTextualPass<'a> {
    arena: Arena<'a>,
}

pub type Document<'a> = DocBuilder<'a, Arena<'a>>;

impl<'a> MirModuleTextualPass<'a> {
    // TODO: Consider moving/deduplicating this from the mir Module pass
    pub fn format_doc_to_string(doc: DocBuilder<'a, Arena<'a>>) -> String {
        let mut w = Vec::new();
        doc.render(80, &mut w)
            .unwrap_or_else(|_| ice!("failed to render mir module"));
        String::from_utf8(w).unwrap()
    }

    pub fn visit_module<'mir: 'a>(&'a self, node: &'mir MirModule<'mir>) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("mir_module")
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(
                        self.arena.intersperse(
                            node.data()
                                .functions()
                                .filter(|f| !f.is_external())
                                .map(|f| self.visit_function(node.data(), f)),
                            self.arena.hardline(),
                        ),
                    )
                    .append(self.arena.hardline())
                    .append(self.arena.hardline())
                    .append(
                        self.arena.intersperse(
                            node.data()
                                .functions()
                                .filter(|f| f.is_external())
                                .map(|f| self.visit_extern_function(node.data(), f)),
                            self.arena.hardline(),
                        ),
                    )
                    .append(self.arena.hardline())
                    .nest(2)
                    .group(),
            )
            .append(self.arena.text("}"))
    }

    pub fn visit_extern_function<'mir: 'a>(
        &'a self,
        _: &'mir MirModuleData<'mir>,
        node: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("mir_extern_function")
            .append(self.arena.space())
            .append(self.arena.text(node.name()))
            .append(self.arena.text("("))
            .append(self.arena.intersperse(
                node.ty().parameters.iter().map(|ty| self.visit_type(ty)),
                self.arena.text(", "),
            ))
            .append(self.arena.text(")"))
            .append(self.arena.space())
            .append(self.arena.text("->"))
            .append(self.arena.space())
            .append(self.visit_type(node.ty().return_type))
            .append(self.arena.text(";"))
    }

    pub fn visit_function<'mir: 'a>(
        &'a self,
        mcx: &'mir MirModuleData<'mir>,
        node: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("mir_function")
            .append(self.arena.space())
            .append(self.arena.text(node.name()))
            .append(self.arena.text("("))
            .append(self.arena.intersperse(
                node.ty().parameters.iter().enumerate().map(|(name, ty)| {
                    self.arena
                        .text(name.to_string())
                        .append(self.arena.text(": "))
                        .append(self.visit_type(ty))
                }),
                self.arena.text(", "),
            ))
            .append(self.arena.text(")"))
            .append(self.arena.space())
            .append(self.arena.text("->"))
            .append(self.arena.space())
            .append(self.visit_type(node.ty().return_type))
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(self.arena.hardline())
            .append(
                self.arena.intersperse(
                    node.data()
                        .blocks()
                        .map(|b| self.visit_basic_block(mcx, node.data(), b)),
                    self.arena.hardline(),
                ),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_basic_block<'mir: 'a>(
        &'a self,
        mcx: &'mir MirModuleData<'mir>,
        fcx: &'mir MirFunctionData<'mir>,
        node: &'mir MirBasicBlock<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text(node.name)
            .append(self.arena.text(":"))
            .append(
                self.arena
                    .hardline()
                    .append(
                        self.arena.intersperse(
                            node.instructions
                                .iter()
                                .map(|i| self.visit_instruction(mcx, fcx, fcx.get_instruction(*i))),
                            self.arena.hardline(),
                        ),
                    )
                    .nest(2)
                    .group(),
            )
    }

    pub fn visit_instruction<'mir: 'a>(
        &'a self,
        mcx: &'mir MirModuleData<'mir>,
        fcx: &'mir MirFunctionData<'mir>,
        node: &'mir MirInstruction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        match node {
            MirInstruction::Alloca(i) => self.visit_alloca_instruction(mcx, fcx, i),
            MirInstruction::Store(i) => self.visit_store_instruction(mcx, fcx, i),
            MirInstruction::Call(i) => self.visit_call_instruction(mcx, fcx, i),
            MirInstruction::Load(i) => self.visit_load_instruction(mcx, fcx, i),
        }
    }

    pub fn visit_alloca_instruction<'mir: 'a>(
        &'a self,
        _: &'mir MirModuleData<'mir>,
        _: &'mir MirFunctionData<'mir>,
        node: &'mir MirAllocaInstruction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("%")
            .append(self.arena.text(node.name))
            .append(self.arena.text(" = "))
            .append(self.arena.text("mem.alloca"))
            .append(self.arena.space())
            .append(self.visit_type(node.alloc_ty))
    }

    pub fn visit_store_instruction<'mir: 'a>(
        &'a self,
        mcx: &'mir MirModuleData<'mir>,
        fcx: &'mir MirFunctionData<'mir>,
        node: &'mir MirStoreInstruction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("mem.store")
            .append(self.arena.space())
            .append(self.visit_value(mcx, fcx, fcx.get_value(node.value)))
            .append(self.arena.text(","))
            .append(self.arena.space())
            .append(self.visit_value(mcx, fcx, fcx.get_value(node.dest)))
    }

    pub fn visit_call_instruction<'mir: 'a>(
        &'a self,
        mcx: &'mir MirModuleData<'mir>,
        fcx: &'mir MirFunctionData<'mir>,
        node: &'mir MirCallInstruction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("%")
            .append(self.arena.text(node.name))
            .append(self.arena.text(" = "))
            .append(self.arena.text("fn.call"))
            .append(self.arena.space())
            .append(self.visit_type(node.ty))
            .append(self.arena.space())
            .append(self.visit_value(mcx, fcx, fcx.get_value(node.callee)))
            .append(self.arena.text("("))
            .append(
                self.arena.intersperse(
                    node.arguments
                        .iter()
                        .map(|a| self.visit_value(mcx, fcx, fcx.get_value(*a))),
                    self.arena.text(","),
                ),
            )
            .append(self.arena.text(")"))
    }

    pub fn visit_load_instruction<'mir: 'a>(
        &'a self,
        mcx: &'mir MirModuleData<'mir>,
        fcx: &'mir MirFunctionData<'mir>,
        node: &'mir MirLoadInstruction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("%")
            .append(self.arena.text(node.name))
            .append(self.arena.text(" = "))
            .append(self.arena.text("mem.load"))
            .append(self.arena.space())
            .append(self.visit_type(node.ty))
            .append(self.arena.text(","))
            .append(self.arena.space())
            .append(self.visit_value(mcx, fcx, fcx.get_value(node.src)))
    }

    pub fn visit_value<'mir: 'a>(
        &'a self,
        mcx: &'mir MirModuleData<'mir>,
        fcx: &'mir MirFunctionData<'mir>,
        node: &'mir MirValue<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        match node {
            MirValue::ConstantInteger32(v) => self.visit_constant_integer_value(mcx, fcx, v),
            MirValue::ConstantBool(v) => self.visit_constant_bool_value(mcx, fcx, v),
            MirValue::Instruction(v) => self.visit_instruction_value(mcx, fcx, v),
            MirValue::Function(v) => self.visit_function_value(mcx, fcx, v),
            MirValue::Argument(_) | MirValue::Label(_) => unimplemented!(),
        }
    }

    pub fn visit_constant_integer_value<'mir: 'a>(
        &'a self,
        _: &'mir MirModuleData<'mir>,
        _: &'mir MirFunctionData<'mir>,
        node: &'mir MirConstantInteger32<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.visit_type(node.ty)
            .append(self.arena.text(" "))
            .append(self.arena.text(node.value.to_string()))
    }

    pub fn visit_constant_bool_value<'mir: 'a>(
        &'a self,
        _: &'mir MirModuleData<'mir>,
        _: &'mir MirFunctionData<'mir>,
        node: &'mir MirConstantBool<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.visit_type(node.ty)
            .append(self.arena.text(" "))
            .append(self.arena.text(node.value.to_string()))
    }

    pub fn visit_instruction_value<'mir: 'a>(
        &'a self,
        _: &'mir MirModuleData<'mir>,
        fcx: &'mir MirFunctionData<'mir>,
        node: &'mir MirInstructionId,
    ) -> DocBuilder<Arena<'a>> {
        self.visit_type(fcx.get_instruction(*node).ty())
            .append(self.arena.space())
            .append(self.arena.text("%"))
            .append(self.arena.as_string(node.0))
    }

    pub fn visit_function_value<'mir: 'a>(
        &'a self,
        mcx: &'mir MirModuleData<'mir>,
        _: &'mir MirFunctionData<'mir>,
        node: &'mir MirFunctionId,
    ) -> DocBuilder<Arena<'a>> {
        self.arena.text(
            mcx.get_function_by_id(*node)
                .expect("missing function")
                .name(),
        )
    }

    pub fn visit_type<'mir: 'a>(&'a self, ty: &'mir MirType) -> DocBuilder<Arena<'a>> {
        match ty {
            MirType::Integer32(_) => self.arena.text("i32"),
            MirType::Bool(_) => self.arena.text("bool"),
            MirType::Void(_) => self.arena.text("void"),
            MirType::Pointer(_) => self.arena.text("ptr"),
            MirType::Function(_) => unreachable!("should not print function types"),
        }
    }
}
