module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawControl
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawControl

/-! The draw's final branches reveal only acceptance and its public retry budget. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomDrawFinishPublic where
  B : Addr
  draws : Nat
  accept : Bool

def RandomDrawFinishPre (p : RandomDrawFinishPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.sp = p.B ∧
  word s.mem p.B Random.oDraws = BitVec.ofNat 64 p.draws ∧
  s.gpr .x8 = BitVec.ofNat 64 (if p.accept then 1 else 0) ∧ 0 < p.draws ∧ p.draws < 2 ^ 64

theorem random_drawFinish_ct : RelCT isa (Two RandomDrawFinishPre) Random.drawFinish (fun _ _ => True) := by
  unfold Random.drawFinish
  refine two_ite (fun p s t hs ht => by
    simp only [eval, State.read, hs.2.2.2.1, ht.2.2.2.1]) ?_ ?_
  · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
  · refine RelCT.seq (two_piece (Ψ := fun p s =>
      s.gpr .x0 = BitVec.ofNat 64 (p.draws - 1)) []
      (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_) ?_
    · intro p s ⟨⟨hs, hsp, hd, _, hpos, hbound⟩, _⟩
      exact WP.mono (random_decrement_ok hs hsp hd hpos hbound)
        (fun _ ⟨ha, _, _⟩ => ha)
    · refine two_ite (fun p s t hs ht => by simp only [eval, State.read, hs, ht]) ?_ ?_
      · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
      · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.AArch64
