module

public import VerifiedGarbage.Proof.Sha3.AArch64.X2Variant
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant

/-!
# Which instances of ML-KEM's AArch64 functions are emitted

`Generic/KeccakX2/Keccak/AArch64/MlKem.lean` is generic over a two-state
permutation `x2` (`KeccakX2`) and a Keccak backend `v` (`Keccak`): paired
sampling and 16-bit arithmetic, which call `x2`'s two- and three-state
functions (`vg_keccak_f1600_x2` and `vg_keccak_f1600_x3`, or the SHA-3
extension's) and `v`'s single-state permutation. It is emitted for every
pair but the baseline `x2` with the SHA-3 backend (`paired`), which the
SHA-3 `x2` with that backend, needing the same CPU features, precedes.
Instances are named by `qualifiedName` from `parts`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.FixedHash.Inst

open VG.Proof.Sha3.AArch64

/-- The functions are emitted for `x2` and `v`: not for the baseline `x2`
with the SHA-3 backend. -/
def paired (x2 : X2Permutation) (v : Permutation) : Bool := x2.sha3 || !v.callee.pairedSha3

/-- The tags and suffixes of the two variants, for `qualifiedName`. -/
def parts (x2 : X2Permutation) (v : Permutation) : List (String × String) :=
  [("x2", x2.suffix), ("keccak", v.callee.suffix)]

end VG.Proof.MlKem.AArch64.FixedHash.Inst
