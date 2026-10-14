module

public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
meta import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant-time parent initialization and DSA return sequence -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum.AArch64

def BasePublic (B : Addr) (s : State) : Prop := s.gpr .x0 = B

theorem pins_base : Pins BasePublic [.x0] :=
  pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)

theorem parent_ct : RelCT isa (Two BasePublic) (.block SignVerify.parent) (fun _ _ => True) :=
  two_taint [.x0] pins_base (by taint_decide)

theorem result_ct : RelCT isa (Two BasePublic) (.block SignVerify.result) (fun _ _ => True) :=
  two_taint [.x0] pins_base (by taint_decide)

end VG.Proof.Dsa.AArch64
