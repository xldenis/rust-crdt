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

// identifier, clock, site id, element
type Entry<T> = (Identifier, Dot<SiteId>, T);

/// LSEQ
///
/// An LSEQ tree is a CRDT for storing sequences of data (Strings, ordered lists).
/// It provides an efficient view of the stored sequence, with fast index, insertion and deletion
/// operations.
///
/// LSEQ [1] is a member of the LOGOOT [2] family of algorithms for CRDT sequences. The major difference
/// with LOGOOT is in the _allocation strategy_ that LSEQ employs to handle insertions.
///
/// Internally, LSEQ views the sequence as the leaves of an ordered, exponential tree. An
/// exponential tree is a tree where the number of childen grows exponentially with the depth of a
/// node. For LSEQ, each layer of the tree doubles the available space. Each child is numbered from
/// 0..2^(3+depth). The first and last child of a node cannot be turned into leaves.
///
/// The path from the root of a tree to a leaf is called the _identifier_ of an element.
///
/// The major challenge for LSEQs is the question of generating new identifiers for insertions.
///
/// If we have the sequence of ordered pairs of identifiers and values `[ ix1: a , ix2: b , ix3: c ]`,
/// and we want to insert `d` at the second position, we must find an identifer ix4 such that
/// ix1 < ix4 < ix2. This ensures that every site will insert d in the same relative position in
/// the sequence even if they dont have ix2 or ix1 yet. The `IdentGen` encapsulates this identifier
/// generation, and ensures that the result is always between the two provided bounds.
///
/// LSEQ is a CmRDT, to guarantee convergence it must see every operation. It also requires that
/// they are delivered in a _causal_ order. Every deletion _must_ be applied _after_ it's
/// corresponding insertion. To guarantee this property, use a causality barrier.
///
/// [1] B. Nédelec, P. Molli, A. Mostefaoui, and E. Desmontils,
/// “LSEQ: an adaptive structure for sequences in distributed collaborative editing,”
/// in Proceedings of the 2013 ACM symposium on Document engineering - DocEng ’13,
/// Florence, Italy, 2013, p. 37, doi: 10.1145/2494266.2494278.
///
/// [2] S. Weiss, P. Urso, and P. Molli,
/// “Logoot: A Scalable Optimistic Replication Algorithm for Collaborative Editing on P2P Networks,”
/// in 2009 29th IEEE International Conference on Distributed Computing Systems,
/// Montreal, Quebec, Canada, Jun. 2009, pp. 404–412, doi: 10.1109/ICDCS.2009.75.

pub struct LSeq<T> {
    seq: Vec<Entry< T>>,
    gen: IdentGen,
    dot: Dot<SiteId>
}

/// Operations that can be performed on an LSeq tree
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "op")]
pub enum Op<T> {
    /// Insert an element
    Insert {
        /// Identifier to insert at
        #[serde(flatten)]
        id: Identifier,
        /// clock of site that issued insertion
        dot: Dot<SiteId>,
        /// Element to insert
        c: T
    },
    /// Delete an element
    Delete{
        /// The original clock information of the insertion we're removing
        remote: Dot<SiteId>,
        #[serde(flatten)]
        /// Identifier to remove
        id: Identifier,
        /// id of site that issued delete
        dot: Dot<SiteId>
    },
}

impl<T : Clone + std::fmt::Debug> LSeq<T> {
    /// Create an LSEQ for the empty string
    pub fn new(id: SiteId) -> Self {
        LSeq { seq: Vec::new(), gen: IdentGen::new(id.0), dot: Dot::new(id, 0) }
    }

    /// Insert an identifier and value in the LSEQ
    pub fn insert(&mut self, ix: Identifier, dot: Dot<SiteId>, c: T) {
        // Inserts only have an impact if the identifier is in the tree
        if let Err(res) = self.seq.binary_search_by(|e| e.0.cmp(&ix)) {
            self.seq.insert(res, (ix, dot, c));
        }
    }

    /// Remove an identifier from the LSEQ
    pub fn delete(&mut self, ix: Identifier) {
        // Deletes only have an effect if the identifier is already in the tree
        if let Ok(i) = self.seq.binary_search_by(|e| e.0.cmp(&ix)) {
            self.seq.remove(i);
        }
    }



    /// Perform a local insertion of an element at a given position.
    /// If `ix` is greater than the length of the LSeq then it is appended to the end.
    pub fn insert_index(&mut self, ix: usize, c: T) -> Op<T> {
        let lower = self.gen.lower();
        let upper = self.gen.upper();

        // If we're inserting past the length of the LSEQ then it's the same as appending.
        let ix_ident = if self.seq.len() <= ix {
            let prev = self.seq.last().map(|(i, _, _)| i).unwrap_or_else(|| &lower);
            self.gen.alloc(prev, &upper)
        } else {
            // To insert an element at position ix, we want it to appear in the sequence between
            // ix - 1 and ix. To do this, retreive each bound defaulting to the lower and upper
            // bounds respectively if they are not found.
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
    pub fn delete_index(&mut self, mut ix: usize) -> Op<T> {
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
    /// Get the string represented by the LSEQ
    pub fn sequence(&self) -> impl Iterator<Item = T> + '_ {
        self.seq.iter().map(|(_, _, c,)| c.clone())
    }

    /// Access the internal representation of the LSEQ
    pub fn raw_entries(&self) -> & Vec<Entry<T>> {
        &self.seq
    }
}

 impl<T : std::fmt::Debug + Clone> CmRDT for LSeq<T> {
     type Op = Op<T>;
    /// Apply an operation to an LSeq instance.
    ///
    /// If the operation is an insert and the identifier is **already** present in the LSEQ instance
    /// the result is a no-op
    ///
    /// If the operation is a delete and the identifier is **not** present in the LSEQ instance the
    /// result is a no-op
    fn apply(&mut self, op: Op<T>){
        match op {
            Op::Insert{id, dot, c} => self.insert(id, dot, c),
            Op::Delete{id,..} => self.delete(id),
        }
    }
 }
