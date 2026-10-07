import VerifiedGarbage.Impl.Bignum.X86_64.AdxRect8
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-! The rectangular tile's addresses depend only on public buffer bases. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

def PublicInputs (values : Reg → BitVec 64) (s : State) : Prop :=
  ∀ r ∈ [.rdi,.rcx,.rbp,.rsi], s.gpr r = values r

theorem tile_ct : RelCT isa (Two PublicInputs) AdxRect8.tile (fun _ _ => True) := by
  apply two_taint [.rdi,.rcx,.rbp,.rsi]
  · intro values s t hs ht r hr
    exact (hs r hr).trans (ht r hr).symm
  · taint_decide

end VG.Proof.Bignum.X86_64.AdxRect8
