import VerifiedGarbage.Impl.Bignum.X86_64.AdxCarry8
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-! Carry values do not affect the addresses or iteration count. -/
namespace VG.Proof.Bignum.X86_64.AdxCarry8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

def PublicInputs (values : Reg → BitVec 64) (s : State) : Prop :=
  ∀ r ∈ [.rsi,.rdx], s.gpr r = values r

theorem propagate_ct : RelCT isa (Two PublicInputs) AdxCarry8.propagate (fun _ _ => True) := by
  apply two_taint [.rsi,.rdx]
  · intro values s t hs ht r hr
    exact (hs r hr).trans (ht r hr).symm
  · taint_decide

end VG.Proof.Bignum.X86_64.AdxCarry8
