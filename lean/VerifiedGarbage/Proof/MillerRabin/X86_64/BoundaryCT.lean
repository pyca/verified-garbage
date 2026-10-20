module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Staging and returning observe only workspace and stack addresses -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.MillerRabin.X86_64

theorem stage_ct : RelCT isa (Two fun B : Addr => fun s : State => s.gpr .rdi = B)
    (.block stage) fun _ _ => True := by
  exact two_taint [.rdi] (fun B s t hs ht r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hs.trans ht.symm) (by taint_decide)

theorem finish_ct : RelCT isa (Two fun p : Addr × Addr => fun s : State =>
    s.gpr .rdi = p.1 ∧ s.gpr .rsp = p.2) (.block finish) fun _ _ => True := by
  exact two_taint [.rdi, .rsp] (fun p s t hs ht r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.trans ht.2.symm) (by taint_decide)

end VG.Proof.MillerRabin.X86_64
