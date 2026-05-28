use base::{hash::Map, index::IndexVec};
use petgraph::{
    algo::is_cyclic_directed,
    dot::Dot,
    graph::{DiGraph, NodeIndex},
};
use span::{Ident, SourceId};
use syntax::ast::{AstVisitor, CompUnit, Item, ModExpr, Program};

pub fn build_module_graph<'ast>(program: &'ast Program<'ast>) -> ModuleGraph {
    log::trace!("[build_module_graph]");
    log::block_in();

    let mut graph = ModuleGraph::default();

    let root_module = graph
        .modules
        .push(Module::new(ModuleKind::Unit(program.unit.source_id)));
    let root_node = graph.dag.add_node(root_module);
    let mut nodes = Map::default();
    nodes.insert(root_module, root_node);

    let mut builder = ModuleGraphBuilder {
        program,
        graph,
        files: Map::default(),
        current_module: root_module,
        name_stack: Vec::default(),
        nodes,
    };
    builder.visit_program(program);
    let graph = builder.graph;

    println!("{:?}", Dot::with_config(&graph.dag, &[]));
    log::block_out();

    graph
}

base::newtype_index! {
    pub struct ModuleId {}
}

base::newtype_index! {
    pub struct DefId {}
}

#[derive(Debug)]
pub struct Def {}

#[derive(Default, Debug)]
pub struct ModuleGraph {
    dag: DiGraph<ModuleId, Ident>,
    modules: IndexVec<ModuleId, Module>,
    defs: IndexVec<DefId, Def>,
}

impl ModuleGraph {}

#[derive(Debug)]
pub struct Module {
    pub kind: ModuleKind,
}

impl Module {
    pub fn new(kind: ModuleKind) -> Self {
        Self { kind }
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum ModuleKind {
    Local,
    Unit(SourceId),
}

/*
  -- file: a.fe
  mod m = {
      mod n = {}
  }
  mod p = {}

  -- file b.fe
  mod z = import "a.fe"

  -- main
  mod q = import "b.fe"
  mod r = import "a.fe"

       Root  --------
      q |            \
        v            |
      SourceId(b)    | r
     z  |            |
        v            |
     SourceId(a) <-_/
    m  |    p \
       v       v
     Local    Local
    n |
      v
    Local
*/

struct ModuleGraphBuilder<'ast> {
    program: &'ast Program<'ast>,

    graph: ModuleGraph,
    files: Map<SourceId, ModuleId>,
    current_module: ModuleId,

    name_stack: Vec<Ident>,

    nodes: Map<ModuleId, NodeIndex>,
}

impl<'ast> ModuleGraphBuilder<'ast> {
    fn make_module(&mut self, name: Option<Ident>, kind: ModuleKind) -> ModuleId {
        let module_id = match kind {
            ModuleKind::Local => self.graph.modules.push(Module::new(kind)),
            ModuleKind::Unit(source_id) => {
                if let Some(module_id) = self.files.get(&source_id) {
                    *module_id
                } else {
                    let module_id = self.graph.modules.push(Module::new(kind));
                    self.files.insert(source_id, module_id);
                    module_id
                }
            }
        };
        println!(
            "ModuleId {module_id:?} : {:?}",
            self.graph.modules[module_id]
        );

        if !self.nodes.contains_key(&module_id) {
            let node_idx = self.graph.dag.add_node(module_id);
            self.nodes.insert(module_id, node_idx);
        }

        if let Some(name) = name {
            self.graph.dag.add_edge(
                self.nodes[&self.current_module],
                self.nodes[&module_id],
                name,
            );

            if is_cyclic_directed(&self.graph.dag) {
                panic!(
                    "Error: cyclic edge {:?} -> {:?} !!",
                    self.current_module, module_id
                );
            }
        }

        module_id
    }

    fn with_module<R>(&mut self, module: ModuleId, f: impl FnOnce(&mut Self) -> R) -> R {
        let old_module = std::mem::replace(&mut self.current_module, module);
        // self.module_stack.push(module);
        let ret = f(self);
        // self.module_stack.pop();
        self.current_module = old_module;
        ret
    }
}

impl<'ast> AstVisitor<'ast> for ModuleGraphBuilder<'ast> {
    fn visit_program(&mut self, program: &'ast Program<'ast>) {
        // for unit in program.imports.values() {
        //     self.visit_comp_unit(unit);
        // }

        self.visit_comp_unit(program.unit);

        self.visit_expr(program.main);
    }

    fn visit_comp_unit(&mut self, unit: &'ast CompUnit<'ast>) {
        for item in unit.items {
            self.visit_item(item);
        }
    }

    fn visit_item(&mut self, item: &'ast Item<'ast>) {
        match item {
            Item::Type(..) => (),
            Item::External(..) => (),
            Item::Func(_, _, expr) => self.visit_expr(expr),
            Item::Mod(id, mod_expr) => {
                self.name_stack.push(id.ident);
                self.visit_mod_expr(mod_expr);
                self.name_stack.pop();
            }
        }
    }

    fn visit_mod_expr(&mut self, mod_expr: &'ast ModExpr<'ast>) {
        match mod_expr {
            ModExpr::Struct(items) => {
                let local_module =
                    self.make_module(self.name_stack.last().copied(), ModuleKind::Local);
                self.with_module(local_module, |self_| {
                    for item in items.iter() {
                        self_.visit_item(item);
                    }
                })
            }
            ModExpr::Path(_) => (),
            ModExpr::Import(source_id) => {
                let unit_module = self.make_module(
                    self.name_stack.last().copied(),
                    ModuleKind::Unit(*source_id),
                );
                let comp_unit = self.program.imports[&source_id];
                self.with_module(unit_module, |self_| self_.visit_comp_unit(comp_unit))
            }
        }
    }
}
