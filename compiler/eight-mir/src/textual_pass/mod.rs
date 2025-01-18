use crate::MirModule;
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

    pub fn visit_module<'hir: 'a>(&'a self, _: &'hir MirModule<'hir>) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("mir_module")
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(self.arena.text("}"))
    }
}
