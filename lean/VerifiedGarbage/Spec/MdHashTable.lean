module

public import VerifiedGarbage.Spec.HashTable

/-!
# Tables of a Merkle–Damgård hash function's compression: the interface `MdHash`

**Trusted** (as every file in `Spec/`). A function that hashes a message
whose length is secret (RSASSA-PSS verification, which finds the salt's
length from the signature) cannot call a hash function's `update` with that
length: it pads the message itself, compresses a public number of blocks,
and keeps the hash value after the last block of the padded message under
a mask. It takes the hash function as a table of the interface `MdHash`
(`FnTable`, `Abi.withTables`): a read-only array of `wordCount`
pointer-sized words (`param`, a `*const [usize; wordCount]`), the
`as_ptr()` of one of the statics of the type `MdHash` that the generated
crate declares (`fn_tables`), holding the addresses of `fns` functions,
which the function calls indirectly (`Code.icall`):

0. the streaming `init`, which sets the hash value to the initial one;
1. the streaming `update`;
2. the streaming `finalize`;
3. the compression function, of whole blocks into the hash value;
4. the digest, from the hash value;

then `dataWords` words of data: the index of the hash function in
`Mgf1.hashes` (`hashAt`, as for `Hash`), its digest length, its block size,
the size of its length field, the size of its streaming state, and 1 if its
length field and words are big-endian (0 if little-endian).

As for `Hash` (`Spec/HashTable.lean`), a contract says what a function
computes with the hash function its table names (`hashAt`). It does not say
what the table's functions do, or what the data after the first two words
hold: the proof of each function taking one runs the code of the functions
of every table of the interface (each table its registration lists, which
the emitter checks is every table of `MdHash`), with each table's own data,
so that it holds only if each table's functions and data compute the hash
function its first word of data names. Which table is passed is public
(`Abi.withTables`): the Rust caller chooses it by the hash function and the
CPU's features.
-/

@[expose] public section

namespace VG.Spec.MdHashTable

open Mgf1 (Hash)

/-- The interface's name: the Rust type of its tables. -/
def iface : String := "MdHash"

/-- The number of functions of a table. -/
def fns : Nat := 5

/-- The number of words of data of a table. -/
def dataWords : Nat := 6

/-- The number of words of a table: its functions', then its data. -/
def wordCount : Nat := fns + dataWords

/-- A parameter taking a table of `MdHash`: a `*const [usize; wordCount]`. -/
def param : Param := .table wordCount

/-- The hash function that the table at `p` in the memory `m` names, on a
target with `ptrBits`-bit pointers: that of `Mgf1.hashes` at the index in
its first word of data (its word `fns`, `ptrBits` bits wide, as
`Abi.tableHeld` lays the words out), if there is one. -/
def hashAt (ptrBits : Nat) (m : Mem) (p : Addr) : Option Hash :=
  Mgf1.hashes[(m.readW (p + BitVec.ofNat 64 (ptrBits / 8 * fns)) ptrBits).toNat]?

/-- The first two words of data of a table of `G`, as for `Hash`: its index
in `Mgf1.hashes`, and its digest length. -/
def dataOf (G : Hash) : List (BitVec 64) := HashTable.dataOf G

end VG.Spec.MdHashTable
