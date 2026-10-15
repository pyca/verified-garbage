module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl

/-! The draw's final branches reveal only acceptance and its public retry budget. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomDrawFinishPublic where
  B : Addr
  draws : Nat
  accept : Bool

def RandomDrawFinishPre (p : RandomDrawFinishPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  word s.mem p.B Random.oDraws = BitVec.ofNat 64 p.draws ∧
  s.zf = some (!p.accept) ∧ 0 < p.draws ∧ p.draws < 2 ^ 64

theorem random_drawFinish_ct : RelCT isa (Two RandomDrawFinishPre) Random.drawFinish (fun _ _ => True) := by
  unfold Random.drawFinish
  refine two_ite (fun p s t hs ht => by simp only [eval, hs.2.2.2.1, ht.2.2.2.1]) ?_ ?_
  · apply two_taint [.rsp] ?_ (by taint_decide)
    intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.1.2.1.trans ht.1.2.1.symm
  · refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rsp = p.B ∧
        s.zf = some (decide (p.draws = 1))) [.rsp] ?_ (by taint_decide) ?_) ?_
    · intro p s t hs ht r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hs.1.2.1.trans ht.1.2.1.symm
    · intro p s ⟨⟨hs, hsp, hd, _, hpos, hbound⟩, _⟩
      exact WP.mono (random_decrement_ok hs hsp hd hpos hbound)
        (fun _ ⟨_, hz, _, hk⟩ => ⟨(hk.gpr (by decide)).trans hsp, hz⟩)
    · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
      · apply two_taint [.rsp] ?_ (by taint_decide)
        intro p s t hs ht r hr
        rw [List.mem_singleton] at hr
        subst r
        exact hs.1.1.trans ht.1.1.symm
      · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.X86_64
