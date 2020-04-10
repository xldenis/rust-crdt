/// Contains the implementation of the exponential tree for LSeq
pub mod ident;

use ident::*;
use serde::{Deserialize, Serialize};

use crate::traits::CmRDT;

use crate::vclock::{Dot, Actor};

// SiteId can be generalized to any A if there is a way to generate a single invalid actor id at every site
// Currently we rely on every site using the Id 0 for that purpose.

/// Actor type for LSEQ sites.
#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SiteId(u32);

// identifier, clock, site id, char
type Entry<T> = (Identifier, Dot<SiteId>, T);

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
pub struct LSeq<T> {
    seq: Vec<Entry< T>>,
    gen: IdentGen,
    dot: Dot<SiteId>
}

/// Operations that can be performed on an LSeq tree
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "op")]
pub enum Op<T> {
    /// Insert a character
    Insert {
        /// Identifier to insert at
        #[serde(flatten)]
        id: Identifier,
        /// clock of site that issued insertion
        dot: Dot<SiteId>,
        /// char to insert
        c: T
    },
    /// Delete a character
    Delete{
        /// ??????
        remote: Dot<SiteId>,
        #[serde(flatten)]
        /// Identifier to remove
        id: Identifier,
        /// id of site that issued delete
        dot: Dot<SiteId>
    },
}

impl<T : Clone> LSeq<T> {
    /// Create an LSeq for the empty string
    pub fn new(id: SiteId) -> Self {
        LSeq { seq: Vec::new(), gen: IdentGen::new(id.0), dot: Dot::new(id, 0) }
    }
    fn do_insert(&mut self, ix: Identifier, dot: Dot<SiteId>, c: T) {
        // Inserts only have an impact if the identifier is in the tree
        if let Err(res) = self.seq.binary_search_by(|e| e.0.cmp(&ix)) {
            self.seq.insert(res, (ix, dot, c));
        }
    }

    fn do_delete(&mut self, ix: Identifier) {
        // Deletes only have an effect if the identifier is already in the tree
        if let Ok(i) = self.seq.binary_search_by(|e| e.0.cmp(&ix)) {
            self.seq.remove(i);
        }
    }

    /// Apply an operation to an LSeq instance.
    pub fn apply(&mut self, op: Op<T>){
        match op {
            Op::Insert{id, dot, c} => self.do_insert(id, dot, c),
            Op::Delete{id,..} => self.do_delete(id),
        }
    }

    /// Perform a local insertion of a character at a given position.
    /// If the ix is greater than the length of the LSeq then it is appended to the end.
    pub fn local_insert(&mut self, ix: usize, c: T) -> Op<T> {
        let lower = self.gen.lower();
        let upper = self.gen.upper();
        // append!
        let ix_ident = if self.seq.len() <= ix {
            let prev = self.seq.last().map(|(i, _, _)| i).unwrap_or_else(|| &lower);
            self.gen.alloc(prev, &upper)
        } else {
            let prev = match ix.checked_sub(1) {
                Some(i) => &self.seq.get(i).unwrap().0,
                None => &lower,
            };
            let next = self.seq.get(ix).map(|(i, _, _)| i).unwrap_or(&upper);
            let a = self.gen.alloc(&prev, next);

            assert!(prev < &a);
            assert!(&a < next);
            a
        };
        let op = Op::Insert{ id: ix_ident, dot: self.dot.clone(), c };
        self.dot.counter += 1;
        self.apply(op.clone());
        op


    }

    /// Perform a local deletion at ix. If ix does not exist then it will delete the last element
    /// of the tree.
    pub fn local_delete(&mut self, mut ix: usize) -> Op<T> {
        if ix >= self.seq.len()  {
            ix = self.seq.len() - 1;
        }
        let data = self.seq[ix].clone();

        let op = Op::Delete{ id: data.0, remote: data.1, dot: self.dot.clone() };

        self.dot.counter += 1;
        self.apply(op.clone());
        op

    }

    /// Get the length of the LSEQ
    pub fn len(&self) -> usize {
        self.seq.len()
    }
    /// Get the string represented by the LSeq tree.
    pub fn sequence(&self) -> impl Iterator<Item = T> + '_ {
        self.seq.iter().map(|(_, _, c,)| c.clone())
    }

    /// Access the internal representation of the LSeq tree
    pub fn raw_entries(&self) -> & Vec<Entry<T>> {
        &self.seq
    }
}

// impl<T : std::fmt::Debug> CmRDT for LSeq<T> {
//     type Op = Op<T>;
//     fn apply(&mut self, op: Self::Op) {
//         self.apply(&op)
//     }
// }
