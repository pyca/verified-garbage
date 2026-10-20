module

public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time parent initialization and DSA return sequence -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64

def BasePublic (B : Addr) (s : State) : Prop := s.gpr .rdi = B

theorem pins_base : Pins BasePublic [.rdi] :=
  pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)

theorem parent_ct : RelCT isa (Two BasePublic) (.block SignVerify.parent) (fun _ _ => True) :=
  two_taint [.rdi] pins_base (by taint_decide)

theorem result_ct : RelCT isa (Two BasePublic) (.block SignVerify.result) (fun _ _ => True) :=
  two_taint [.rdi] pins_base (by taint_decide)

theorem save_ct : RelCT isa (Two (fun (B : Addr) (s : State) => s.gpr .r11 = B))
    (.block SignVerify.save) (fun _ _ => True) :=
  two_taint [.r11] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

end VG.Proof.Dsa.X86_64
