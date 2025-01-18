use crate::instruction::{
    MirAllocaInstruction, MirCallInstruction, MirInstruction, MirLoadInstruction,
    MirStoreInstruction,
};
use crate::ty::MirType;
use crate::value::{MirConstantInteger, MirValue};
use crate::{MirBasicBlock, MirFunction, MirModule};
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

    pub fn visit_module<'mir: 'a>(
        &'a self,
        module: &'mir MirModule<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("mir_module")
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(
                        self.arena.intersperse(
                            module
                                .functions
                                .iter()
                                .filter(|f| !f.is_external())
                                .map(|f| self.visit_function(f)),
                            self.arena.hardline(),
                        ),
                    )
                    .append(self.arena.hardline())
                    .append(self.arena.hardline())
                    .append(
                        self.arena.intersperse(
                            module
                                .functions
                                .iter()
                                .filter(|f| f.is_external())
                                .map(|f| self.visit_extern_function(f)),
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
        function: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("mir_extern_function")
            .append(self.arena.space())
            .append(self.arena.text(function.name))
            .append(self.arena.text("("))
            .append(self.arena.intersperse(
                function.ty.parameters.iter().enumerate().map(|(name, ty)| {
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
            .append(self.visit_type(function.ty.return_type))
            .append(self.arena.text(";"))
    }

    pub fn visit_function<'mir: 'a>(
        &'a self,
        function: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("mir_function")
            .append(self.arena.space())
            .append(self.arena.text(function.name))
            .append(self.arena.text("("))
            .append(self.arena.intersperse(
                function.ty.parameters.iter().enumerate().map(|(name, ty)| {
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
            .append(self.visit_type(function.ty.return_type))
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(self.arena.hardline())
            .append(
                self.arena.intersperse(
                    function
                        .blocks
                        .values()
                        .map(|b| self.visit_basic_block(b, function)),
                    self.arena.hardline(),
                ),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_basic_block<'mir: 'a>(
        &'a self,
        block: &'mir MirBasicBlock<'mir>,
        owner: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text(block.name)
            .append(self.arena.text(":"))
            .append(
                self.arena
                    .hardline()
                    .append(self.arena.intersperse(
                        block.instructions.iter().map(|i| {
                            let inst = owner
                                .get_instruction(*i)
                                .expect("malformed mir: missing instruction reference");
                            self.visit_instruction(inst, owner)
                        }),
                        self.arena.hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
    }

    pub fn visit_instruction<'mir: 'a>(
        &'a self,
        instruction: &'mir MirInstruction<'mir>,
        owner: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        match instruction {
            MirInstruction::Alloca(i) => self.visit_alloca_instruction(i, owner),
            MirInstruction::Store(i) => self.visit_store_instruction(i, owner),
            MirInstruction::Call(i) => self.visit_call_instruction(i, owner),
            MirInstruction::Load(i) => self.visit_load_instruction(i, owner),
        }
    }

    pub fn visit_alloca_instruction<'mir: 'a>(
        &'a self,
        instruction: &'mir MirAllocaInstruction<'mir>,
        owner: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("%")
            .append(self.arena.text(instruction.name))
            .append(self.arena.text(" = "))
            .append(self.arena.text("mem.alloca"))
            .append(self.arena.space())
            .append(self.visit_type(instruction.alloc_ty))
    }

    pub fn visit_store_instruction<'mir: 'a>(
        &'a self,
        instruction: &'mir MirStoreInstruction<'mir>,
        owner: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        let value = owner
            .get_value(instruction.value)
            .expect("malformed mir: missing value reference");
        let dest = owner
            .get_value(instruction.dest)
            .expect("malformed mir: missing value reference");

        self.arena
            .text("%")
            .append(self.arena.text(instruction.name))
            .append(self.arena.text(" = "))
            .append(self.arena.text("mem.store"))
            .append(self.arena.space())
            .append(self.visit_value(value, owner))
            .append(self.arena.text(","))
            .append(self.arena.space())
            .append(self.visit_value(dest, owner))
    }

    pub fn visit_call_instruction<'mir: 'a>(
        &'a self,
        instruction: &'mir MirCallInstruction<'mir>,
        owner: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("%")
            .append(self.arena.text(instruction.name))
            .append(self.arena.text(" = "))
            .append(self.arena.text("fn.call"))
            .append(self.arena.space())
            .append(self.visit_type(instruction.ty))
            .append(self.arena.space())
            .append(self.visit_value(
                owner.get_value(instruction.callee).expect("missing callee"),
                owner,
            ))
            .append(self.arena.text("("))
            .append(self.arena.intersperse(
                instruction.arguments.iter().map(|a| {
                    self.visit_value(owner.get_value(*a).expect("missing argument"), owner)
                }),
                self.arena.text(","),
            ))
            .append(self.arena.text(")"))
    }

    pub fn visit_load_instruction<'mir: 'a>(
        &'a self,
        instruction: &'mir MirLoadInstruction<'mir>,
        owner: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("%")
            .append(self.arena.text(instruction.name))
            .append(self.arena.text(" = "))
            .append(self.arena.text("mem.load"))
            .append(self.arena.space())
            .append(self.visit_type(instruction.ty))
            .append(self.arena.space())
            .append(self.visit_value(
                owner.get_value(instruction.src).expect("missing src"),
                owner,
            ))
    }

    pub fn visit_value<'mir: 'a>(
        &'a self,
        value: &'mir MirValue<'mir>,
        owner: &'mir MirFunction<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        match value {
            MirValue::ConstantInteger(v) => self.visit_constant_integer_value(v),
            MirValue::Instruction(v) => self
                .visit_type(owner.get_instruction(*v).expect("missing instruction").ty())
                .append(self.arena.space())
                .append(self.arena.text("%"))
                .append(self.arena.as_string(v.0)),
            MirValue::Function(v) => self.arena.as_string(v.0),
            MirValue::Argument(_) | MirValue::Label(_) => unimplemented!(),
        }
    }

    pub fn visit_constant_integer_value<'mir: 'a>(
        &'a self,
        value: &'mir MirConstantInteger<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.visit_type(value.ty)
            .append(self.arena.text(" "))
            .append(self.arena.text(value.value.to_string()))
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
