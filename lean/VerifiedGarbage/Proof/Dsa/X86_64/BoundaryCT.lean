import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs

/-! # Constant-time parent initialization and DSA return sequence -/
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

end VG.Proof.Dsa.X86_64
