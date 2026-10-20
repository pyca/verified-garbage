module

public import VerifiedGarbage.Proof.Sha3.AArch64.X2Variant
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant

/-!
# Which instances of ML-KEM's AArch64 functions are emitted

`Generic/KeccakX2/Keccak/AArch64/MlKem.lean` is generic over a two-state
permutation `x2` (`KeccakX2`) and a Keccak backend `v` (`Keccak`). Its paired
path calls `vg_keccak_f1600_x2_sha3` (and `vg_keccak_f1600_x3_sha3`), so it is
emitted for the `x2` with the SHA-3 extension (`paired`), with each backend's
single-state permutation; its sponge path (one state at a time, over the
backend's sponge functions) for the baseline `x2` and the baseline backend
only (`sponge`); and nothing for the baseline `x2` with the SHA-3 backend.
Instances are named by `Emit.qualifiedName` from `parts`, and need both
variants' CPU features (`features`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.FixedHash.Inst

open VG.Proof.Sha3.AArch64

/-- The paired path is emitted: `x2` is the permutation it calls. -/
def paired (x2 : X2Permutation) : Bool := x2.sha3

/-- The sponge path is emitted: both variants are the baseline. -/
def sponge (x2 : X2Permutation) (v : Permutation) : Bool := !x2.sha3 && !v.callee.pairedSha3

/-- The tags and suffixes of the two variants, for `Emit.qualifiedName`. -/
def parts (x2 : X2Permutation) (v : Permutation) : List (String × String) :=
  [("x2", x2.suffix), ("keccak", v.callee.suffix)]

/-- The CPU features of both variants. -/
def features (x2 : X2Permutation) (v : Permutation) : List String :=
  x2.features ++ v.features.filter (!x2.features.contains ·)

end VG.Proof.MlKem.AArch64.FixedHash.Inst
