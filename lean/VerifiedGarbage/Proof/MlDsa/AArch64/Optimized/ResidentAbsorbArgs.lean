import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentZero
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskEnv

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (Only wp_addImm)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (absorb)

private theorem args_ok (s : State) :
    WP isa (.block [.addImm .x .x2 .x19 0,.addImm .x .x3 .x20 0,.addImm .x .x4 .x3 66]) s
      fun t => Only [.x2,.x3,.x4] s t ∧ t.gpr .x2=s.gpr .x19 ∧
        t.gpr .x3=s.gpr .x20 ∧ t.gpr .x4=s.gpr .x20+66 := by
  refine wp_addImm (by decide) fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_addImm (by decide) fun t ht et => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((ha.trans hb).trans ht).mono (by simp)
  · rw [ht.get .x2,hb.get .x2,ea]; exact BitVec.add_zero _
  · rw [ht.get .x3,eb,ha.get .x20]; exact BitVec.add_zero _
  · rw [et,eb,ha.get .x20,BitVec.add_zero]; rfl

/-- Absorb the two independent 66-byte seeds into the single paired state. -/
theorem absorb0_ok (s : State)
    (hin : (Region.mk (s.gpr .x20) 132)∈s.rd++s.wr)
    (hw : (Region.mk (s.gpr .x19) 8192)∈s.wr)
    (hsep : (Region.mk (s.gpr .x20) 132).Disjoint ⟨s.gpr .x19,400⟩)
    (hz : ∀ i<25, s.mem.read (wordAddr (s.gpr .x19) i) 16=0) :
    WP isa (.block (absorb 0)) s fun t => RegKeep [.x2,.x3,.x4,.x6,.x7,.x8,.x9] s t ∧
      Frame [pairR (s.gpr .x19)] s.mem t.mem ∧
      PairAt t.mem (s.gpr .x19) (seedState s.mem (s.gpr .x20)) (seedState s.mem (s.gpr .x20+66)) := by
  unfold absorb
  simp only [Nat.mul_zero]
  rw [WP.block_append_iff]
  refine WP.mono (args_ok s) ?_
  intro a ⟨ha,h2,h3,h4⟩
  have input (off len : Nat) (hb : off+len≤132) :
      InRegions (a.rd++a.wr) (s.gpr .x20+BitVec.ofNat 64 off) len := by
    rw [ha.rd,ha.wr]
    exact ⟨_,hin,Offset.contains_base _ hb (by omega)⟩
  refine WP.mono (absorbBody_ok h2 h3 h4
    (fun j hj => input (8*j) 8 (by omega))
    (fun j hj => by
      change InRegions _ (s.gpr .x20+BitVec.ofNat 64 66+BitVec.ofNat 64 (8*j)) 8
      rw [Offset.add_add]; exact input (66+8*j) 8 (by omega))
    (input 64 1 (by decide)) (input 65 1 (by decide))
    (by change InRegions _ (s.gpr .x20+BitVec.ofNat 64 66+BitVec.ofNat 64 64) 1
        rw [Offset.add_add]; exact input (66+64) 1 (by decide))
    (by change InRegions _ (s.gpr .x20+BitVec.ofNat 64 66+BitVec.ofNat 64 65) 1
        rw [Offset.add_add]; exact input (66+65) 1 (by decide))
    (fun j hj => by rw [ha.wr]; exact ⟨_,hw,Offset.contains_base _ (by omega) (by omega)⟩)
    (hsep.sub_left (Region.sub_prefix (by decide)))
    (hsep.sub_left (Offset.sub_base _ (by decide)))
    (by simpa only [ha.mem] using hz)) ?_
  intro t ⟨ht,hf,hpair⟩
  refine ⟨((RegKeep.only ha).trans ht).mono (by simp),?_,?_⟩
  · simpa only [ha.mem] using hf
  · simpa only [ha.mem] using hpair

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
