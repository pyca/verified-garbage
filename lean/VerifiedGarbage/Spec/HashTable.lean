module

public import VerifiedGarbage.Spec.Mgf1
public import VerifiedGarbage.TCB.Sig

/-!
# Tables of a hash function: the interface `Hash`

**Trusted** (as every file in `Spec/`). A function generic over a hash
function takes it as a table of functions (`FnTable`, `Abi.withTables`) of
the interface `Hash`: a read-only array of `wordCount` `u64`s (`param`),
the `words()` of one of the statics of the type `Hash` that the generated
crate declares (`fn_tables`), holding the addresses of `fns` functions (the
hash function's streaming functions, which the function calls indirectly,
`Code.icall`), then two words of data (`dataOf`): the index of the hash
function in `Mgf1.hashes`, and its digest length `hLen` in octets.

A contract says what a function computes with the hash function its table
names (`hashAt`). It does not say what the table's functions do: the proof
of each function taking one runs the code of the functions of every table
of the interface (each table its registration lists, `Artifact.tables`,
which the emitter checks is every table of `Hash`), so that it holds only
if each table's functions compute the hash function its data names. Which
table is passed is public (`Abi.withTables`): the Rust caller chooses it by
the hash function and the CPU's features.
-/

@[expose] public section

namespace VG.Spec.HashTable

open Mgf1 (Hash)

/-- The interface's name: the Rust type of its tables. -/
def iface : String := "Hash"

/-- The number of functions of a table. -/
def fns : Nat := 3

/-- The number of words of a table: its functions', then two of data. -/
def wordCount : Nat := fns + 2

/-- A parameter taking a table of `Hash`: a `*const [u64; wordCount]`. -/
def param : Param := .array false .u64 wordCount

/-- The index of `G` in `Mgf1.hashes`, by its Rust name, which is distinct
for each. -/
def index (G : Hash) : Nat := Mgf1.hashes.findIdx (·.rust == G.rust)

/-- The data of a table of `G`: its index in `Mgf1.hashes`, and its digest
length. -/
def dataOf (G : Hash) : List (BitVec 64) := [BitVec.ofNat 64 (index G), BitVec.ofNat 64 G.len]

/-- The hash function that the table at `p` in the memory `m` names: that of
`Mgf1.hashes` at the index in its first word of data, if there is one. -/
def hashAt (m : Mem) (p : Addr) : Option Hash :=
  Mgf1.hashes[(m.readW (p + BitVec.ofNat 64 (8 * fns)) 64).toNat]?

/-- Each hash function's `index` is its position in `Mgf1.hashes` (their
Rust names are distinct), so a table holding `dataOf G` names `G`. -/
theorem index_hashes : (Mgf1.hashes.map fun G => index G) = List.range Mgf1.hashes.length := by
  decide

end VG.Spec.HashTable
