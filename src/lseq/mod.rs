/// Contains the implementation of the exponential tree for LSeq
pub mod ident;

use ident::*;
use serde::{Deserialize, Serialize};

use crate::traits::CmRDT;

// identifier, clock, site id, char
type Entry = (Identifier, u64, u32, char);

/// LSeq tree
///
/// An LSeq tree is a CRDT for storing sequences of data (Strings, ordered lists)
/// Internally it works by viewing each character as the leaf of a giant tree.
/// The path that leads to a given character is called the 'identifier' of that character
///
/// LSeq is very similar to the LOGOOT algorithm for representing sequences. The major change is
/// that LSeq uses an **exponential** tree to store data. That means that at each level of the tree
/// the space doubles. This helps prevent growth of identifier sizes.
//#[derive(Serialize, Deserialize)]
pub struct LSeq {
    text: Vec<Entry>, // gen: NameGenerator
    gen: IdentGen,
    clock: u64,
}

/// Operations that can be performed on an LSeq tree
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "op")]
pub enum Op {
    /// Insert a character
    Insert {
        /// Identifier to insert at
        #[serde(flatten)]
        id: Identifier,
        /// clock of site that issued insertion
        clock: u64,
        /// id of site that issued insertion
        site_id: u32,
        /// char to insert
        c: char
    },
    /// Delete a character
    Delete{
        /// ??????
        remote: (u32, u64),
        #[serde(flatten)]
        /// Identifier to remove
        id: Identifier,
        /// id of site that issued delete
        site_id: u32,
        /// clock of site that issued delete
        clock: u64
    },
}

impl LSeq {
    /// Create an LSeq for the empty string
    pub fn new(id: u32) -> Self {
        LSeq { text: Vec::new(), gen: IdentGen::new(id), clock: 0 }
    }
    fn do_insert(&mut self, ix: Identifier, clock: u64, site_id: u32, c: char) {
        // Inserts only have an impact if the identifier is in the tree
        if let Err(res) = self.text.binary_search_by(|e| e.0.cmp(&ix)) {
            self.text.insert(res, (ix, clock, site_id, c));
        }
    }

    fn do_delete(&mut self, ix: &Identifier) {
        // Deletes only have an effect if the identifier is already in the tree
        if let Ok(i) = self.text.binary_search_by(|e| e.0.cmp(&ix)) {
            self.text.remove(i);
        }
    }

    /// Apply an operation to an LSeq instance.
    pub fn apply(&mut self, op: &Op){
        match op {
            Op::Insert{id, clock, site_id, c} => self.do_insert(id.clone(), *clock, *site_id, *c),
            Op::Delete{id,..} => self.do_delete(id),
        }
    }

    /// Perform a local insertion of a character at a given position.
    /// If the ix is greater than the length of the LSeq then it is appended to the end.
    pub fn local_insert(&mut self, ix: usize, c: char) -> Op {
        let lower = self.gen.lower();
        let upper = self.gen.upper();
        // append!
        let ix_ident = if self.text.len() <= ix {
            let prev = self.text.last().map(|(i, _, _, _)| i).unwrap_or_else(|| &lower);
            self.gen.alloc(prev, &upper)
        } else {
            let prev = match ix.checked_sub(1) {
                Some(i) => &self.text.get(i).unwrap().0,
                None => &lower,
            };
            let next = self.text.get(ix).map(|(i, _, _, _)| i).unwrap_or(&upper);
            let a = self.gen.alloc(&prev, next);

            assert!(prev < &a);
            assert!(&a < next);
            a
        };
        let op = Op::Insert{ id: ix_ident, clock: self.clock, site_id: self.gen.site_id, c };
        self.clock += 1;
        self.apply(&op);
        op


    }

    /// Perform a local deletion at ix. If ix does not exist then it will delete the last element
    /// of the tree.
    pub fn local_delete(&mut self, mut ix: usize) -> Op {
        if ix >= self.text.len()  {
            ix = self.text.len() - 1;
        }
        let data = self.text[ix].clone();

        let op = Op::Delete{ id: data.0, remote: (data.2, data.1), clock: self.clock, site_id: self.gen.site_id };

        self.clock += 1;
        self.apply(&op);
        op

    }

    /// Get the string represented by the LSeq tree.
    pub fn text(&self) -> String {
        self.text.iter().map(|(_, _, _, c,)| c).collect::<String>()
    }

    /// Access the internal representation of the LSeq tree
    pub fn raw_text(&self) -> & Vec<Entry> {
        &self.text
    }
}

impl CmRDT for LSeq {
    type Op = Op;
    fn apply(&mut self, op: Self::Op) {
        self.apply(&op)
    }
}
