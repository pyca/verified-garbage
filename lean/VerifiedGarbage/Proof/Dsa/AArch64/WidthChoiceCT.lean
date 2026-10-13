module

public import VerifiedGarbage.Proof.Dsa.AArch64.WidthChoice
meta import VerifiedGarbage.Proof.Dsa.AArch64.WidthChoice
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant time of the supported public-width switch -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def WidthChoicePre (p : Nat × Nat) (s : State) : Prop :=
  s.gpr .x10 = BitVec.ofNat 64 p.1 ∧ s.gpr .x8 = BitVec.ofNat 64 p.2

/-- The switch branches only on the public p width in `x10`. -/
theorem widthChoice_ct : RelCT isa (Two WidthChoicePre) Checks.widthChoice (fun _ _ => True) :=
  two_taint [.x10] (pins_of (fun p _ => BitVec.ofNat 64 p.1) (by
    intro p s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1)) (by taint_decide)

end VG.Proof.Dsa.AArch64
