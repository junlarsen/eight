use crate::ty::MirType;
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
                    .append("// module functions")
                    .append(self.arena.hardline())
                    .append(
                        self.arena.intersperse(
                            module
                                .functions
                                .values()
                                .filter(|f| !f.is_external())
                                .map(|f| self.visit_function(f)),
                            self.arena.hardline(),
                        ),
                    )
                    .append(self.arena.hardline())
                    .append(self.arena.hardline())
                    .append("// module extern functions")
                    .append(self.arena.hardline())
                    .append(
                        self.arena.intersperse(
                            module
                                .functions
                                .values()
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
            .append(self.arena.text("@"))
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
            .append(self.arena.text("@"))
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
            .append(self.arena.intersperse(
                function.blocks.values().map(|b| self.visit_basic_block(b)),
                self.arena.hardline(),
            ))
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_basic_block<'mir: 'a>(
        &'a self,
        block: &'mir MirBasicBlock<'mir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text(block.name)
            .append(self.arena.text(":"))
            .append(
                self.arena
                    .hardline()
                    .append(self.arena.text("mov a b"))
                    .nest(2)
                    .group(),
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
