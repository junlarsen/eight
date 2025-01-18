use crate::ty::MirType;
use crate::{MirFunction, MirModule};
use eight_diagnostics::ice;
use pretty::{Arena, DocAllocator, DocBuilder};

#[derive(Default)]
pub struct MirModuleTextualPass<'a> {
    arena: Arena<'a>,
}

pub type Document<'a> = DocBuilder<'a, Arena<'a>>;

impl<'a> MirModuleTextualPass<'a> {
    // TODO: Consider moving/deduplicating this from the HIR Module pass
    pub fn format_doc_to_string(doc: DocBuilder<'a, Arena<'a>>) -> String {
        let mut w = Vec::new();
        doc.render(80, &mut w)
            .unwrap_or_else(|_| ice!("failed to render hir module"));
        String::from_utf8(w).unwrap()
    }

    pub fn visit_module<'hir: 'a>(
        &'a self,
        module: &'hir MirModule<'hir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("mir_module")
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append("// module functions")
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

    pub fn visit_extern_function<'hir: 'a>(
        &'a self,
        function: &'hir MirFunction<'hir>,
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

    pub fn visit_function<'hir: 'a>(
        &'a self,
        function: &'hir MirFunction<'hir>,
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
            .append(
                self.arena
                    .hardline()
                    .append(self.arena.text("body"))
                    .nest(2)
                    .group(),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_type<'hir: 'a>(&'a self, ty: &'hir MirType) -> DocBuilder<Arena<'a>> {
        match ty {
            MirType::Integer32(_) => self.arena.text("i32"),
            MirType::Bool(_) => self.arena.text("bool"),
            MirType::Void(_) => self.arena.text("void"),
            MirType::Pointer(_) => self.arena.text("ptr"),
            MirType::Function(_) => unreachable!("should not print function types"),
        }
    }
}
