module

public import VerifiedGarbage.Spec.Mgf1
public import VerifiedGarbage.TCB.Sig

/-!
# A hash function in the data of a table of functions

**Trusted** (as every file in `Spec/`). A table of functions that names a
hash function of `Mgf1.hashes` (one of `MdHash`, `Spec/MdHashTable.lean`, or
of `Hmac`, `Spec/HmacTable.lean`) starts its data with two words
(`dataOf`): the index of the hash function in `Mgf1.hashes` (`index`), and
its digest length `hLen` in octets.
-/

@[expose] public section

namespace VG.Spec.HashTable

open Mgf1 (Hash)

/-- The index of `G` in `Mgf1.hashes`, by its Rust name, which is distinct
for each. -/
def index (G : Hash) : Nat := Mgf1.hashes.findIdx (·.rust == G.rust)

/-- The first two words of data of a table naming `G`: its index in
`Mgf1.hashes`, and its digest length. -/
def dataOf (G : Hash) : List (BitVec 64) := [BitVec.ofNat 64 (index G), BitVec.ofNat 64 G.len]

end VG.Spec.HashTable
