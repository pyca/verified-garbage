module

public import VerifiedGarbage.Spec.Mgf1

/-!
# The numbers of the hash functions

**Trusted** (as every file in `Spec/`). The number that names each hash
function of `Mgf1.hashes` to the Rust functions that take the hash function
as an argument (a public `u32`) rather than in their name.
-/

@[expose] public section

namespace VG.Spec.Mgf1

/-- The hash function the number `i` names: its index in `hashes`, from 0 for
MD5 to 13 for BLAKE2s-256, which is `RsaPkcs1Sig.Hash.ofId`'s numbering
where both name one. -/
def ofId (i : Nat) : Option Hash := hashes[i]?

end VG.Spec.Mgf1
