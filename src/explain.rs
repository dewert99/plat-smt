use batsat::Lit;
use std::fmt::Debug;
use std::mem;
use std::ops::Deref;

use batsat::LSet;
use egg::raw::RawEGraph;
use egg::{Id, Language};
use hashbrown::HashSet;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct Justification(Lit);

enum EJustification {
    Lit(Lit),
    Congruence,
    NoOp,
}

impl Justification {
    pub fn from_lit(l: Lit) -> Self {
        debug_assert!(l != Lit::UNDEF);
        debug_assert!(l != Lit::ERROR);
        Justification(l)
    }

    pub const CONGRUENCE: Self = Justification(Lit::ERROR);

    pub const NOOP: Self = Justification(Lit::UNDEF);

    fn expand(self) -> EJustification {
        match self.0 {
            Lit::ERROR => EJustification::Congruence,
            Lit::UNDEF => EJustification::NoOp,
            l => EJustification::Lit(l),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Connection {
    next: Id,
    justification: Justification,
}

impl Connection {
    #[inline]
    fn end(node: Id) -> Self {
        Connection {
            next: node,
            justification: Justification::CONGRUENCE,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Explain {
    explainfind: Vec<Connection>,
    undo_log: UndoLog,
}

pub(crate) struct ExplainWith<'a, X> {
    explain: &'a Explain,
    raw: X,
}

impl Explain {
    pub(crate) fn add(&mut self, set: Id) -> Id {
        debug_assert_eq!(self.explainfind.len(), usize::from(set));
        self.explainfind.push(Connection::end(set));
        set
    }

    // reverse edges recursively to make this node the leader
    fn set_parent(&mut self, node: Id, parent: Connection) {
        let mut prev = node;
        let mut curr = mem::replace(&mut self.explainfind[usize::from(prev)], parent);
        let mut count = 0;
        while prev != curr.next {
            let pconnection = Connection {
                justification: curr.justification,
                next: prev,
            };
            let next = mem::replace(&mut self.explainfind[usize::from(curr.next)], pconnection);
            prev = curr.next;
            curr = next;
            count += 1;
            debug_assert!(count < 1000);
        }
    }

    pub(crate) fn union(&mut self, node1: Id, node2: Id, justification: Justification) {
        let pconnection = Connection {
            justification: justification.clone(),
            next: node2,
        };

        self.set_parent(node1, pconnection);

        self.undo_log_union(node1, node2);
    }

    pub(crate) fn with_raw_egraph<X>(&self, raw: X) -> ExplainWith<'_, X> {
        ExplainWith { explain: self, raw }
    }
}

impl<'a, X> Deref for ExplainWith<'a, X> {
    type Target = Explain;

    fn deref(&self) -> &Self::Target {
        self.explain
    }
}

impl<'x, L: Language, D, U> ExplainWith<'x, &'x RawEGraph<L, D, U>> {
    pub(crate) fn node(&self, node_id: Id) -> &L {
        self.raw.id_to_node(node_id)
    }

    fn common_ancestor(&self, mut left: Id, mut right: Id) -> Id {
        let mut seen_left: HashSet<Id> = Default::default();
        let mut seen_right: HashSet<Id> = Default::default();
        loop {
            seen_left.insert(left);
            if seen_right.contains(&left) {
                return left;
            }

            seen_right.insert(right);
            if seen_left.contains(&right) {
                return right;
            }

            let next_left = self.explainfind[usize::from(left)].next;
            let next_right = self.explainfind[usize::from(right)].next;
            debug_assert!(next_left != left || next_right != right);
            left = next_left;
            right = next_right;
        }
    }

    fn get_connections(&self, mut node: Id, ancestor: Id, res: &mut LSet) {
        if node == ancestor {
            return;
        }

        let mut pre_congrence = node;

        loop {
            let connection = &self.explainfind[usize::from(node)];
            let next = connection.next;
            match connection.justification.expand() {
                EJustification::Lit(l) => {
                    res.insert(l);
                    self.handle_congruence(pre_congrence, node, res);
                    pre_congrence = next;
                }
                EJustification::NoOp => {
                    self.handle_congruence(pre_congrence, node, res);
                    pre_congrence = next;
                }
                EJustification::Congruence => {}
            }
            if next == ancestor {
                self.handle_congruence(pre_congrence, next, res);
                return;
            }
            debug_assert_ne!(next, node);
            node = next;
        }
    }

    fn handle_congruence(&self, left: Id, right: Id, res: &mut LSet) {
        if left == right {
            return;
        }

        let current_node = self.node(left);
        let next_node = self.node(right);
        debug_assert!(current_node.matches(next_node));

        for (left_child, right_child) in current_node
            .children()
            .iter()
            .zip(next_node.children().iter())
        {
            self.explain_equivalence(*left_child, *right_child, res)
        }
    }

    pub fn explain_equivalence(&self, left: Id, right: Id, res: &mut LSet) {
        debug_assert_eq!(self.raw.find(left), self.raw.find(right));
        let ancestor = self.common_ancestor(left, right);
        self.get_connections(left, ancestor, res);
        self.get_connections(right, ancestor, res);
    }
}

pub(super) type UndoLog = Vec<(Id, Id)>;

#[derive(Default, Clone, Debug)]
pub(crate) struct PushInfo(usize);

impl Explain {
    pub(super) fn undo_log_union(&mut self, node1: Id, node2: Id) {
        self.undo_log.push((node1, node2))
    }

    pub(crate) fn push(&self) -> PushInfo {
        PushInfo(self.undo_log.len())
    }

    pub(crate) fn pop(&mut self, info: PushInfo, old_nodes: usize) {
        for (id1, id2) in self.undo_log.drain(info.0..).rev() {
            let mut did_something = false;

            let connection1 = &mut self.explainfind[usize::from(id1)];
            if connection1.next == id2 {
                *connection1 = Connection::end(id1);
                did_something = true;
            }
            let connection2 = &mut self.explainfind[usize::from(id2)];
            if connection2.next == id1 {
                *connection2 = Connection::end(id2);
                did_something = true;
            }
            debug_assert!(did_something)
        }
        self.explainfind.truncate(old_nodes);
    }

    pub(crate) fn clear(&mut self) {
        self.undo_log.clear();
        self.explainfind.clear();
    }
}
