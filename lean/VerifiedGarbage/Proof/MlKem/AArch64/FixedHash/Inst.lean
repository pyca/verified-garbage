module

public import VerifiedGarbage.Proof.Sha3.AArch64.X2Variant
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.Variants.KeccakX2.AArch64
public import VerifiedGarbage.Proof.Variants.Keccak.AArch64

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

/-- The pairs of implementations the functions are emitted for, best first:
every two-state implementation with every single-state one, but the baseline
two-state one with the SHA-3 backend (`paired`). -/
def variants : List (X2Permutation × Permutation) :=
  (VG.Proof.Variants.KeccakX2.AArch64.variants.flatMap fun x2 =>
    VG.Proof.Variants.Keccak.AArch64.variants.map fun v => (x2, v)).filter fun xv => paired xv.1 xv.2

end VG.Proof.MlKem.AArch64.FixedHash.Inst
