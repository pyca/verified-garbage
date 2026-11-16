module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.AArch64.KgA
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# ML-KEM on AArch64: `keygen`, the polynomial buffers of `ŝ`, `ê` and `t̂`

Where a polynomial buffer of the computation of `ŝ`, `ê` and `t̂` may be in
`scratch` (`PolyOff`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- A polynomial buffer in `scratch` for phase C: past `Â`'s start, below
the saved registers. -/
def PolyOff (P : KemLay) (off : Nat) : Prop := AH ≤ off ∧ off + 1024 ≤ SV P

end VG.Proof.MlKem.AArch64.KeyGen
