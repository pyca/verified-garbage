import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailUpperFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailFirst

/-! ## From `CommitTailUpperInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_movz)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def seedNonceState (m : Mem) (p : Addr) (k : BitVec 64) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val<8 then m.readW (p+BitVec.ofNat 64 (8*i.val)) 64
    else if i.val=8 then nonceWord k else if i.val=16 then 0x8000000000000000 else 0

theorem seedNonceState_eq (B : Spec.Sha3.State) (m : Mem) (p : Addr) (k : BitVec 64) :
    replaceWord (replaceWord (clearPrefix (seedPrefix B m p 8) 17) 8 (nonceWord k))
      16 0x8000000000000000 = seedNonceState m p k := by
  apply Vector.ext
  intro i hi
  rw [← VG.Proof.Sha3.getElem!_eq _ hi,replaceWord_get _ _ _ _ hi,
    replaceWord_get _ _ _ _ hi,clearPrefix_get _ _ _ hi,seedPrefix_get _ _ _ _ _ hi]
  simp only [seedNonceState,Vector.getElem_ofFn]
  by_cases h8 : i<8
  · simp only [h8,ite_true,show ¬ i=16 by omega,show ¬ i=8 by omega,
      show ¬ (8≤i ∧ i<8+17) by omega,ite_false]
  · by_cases he8 : i=8
    · subst i; simp only [ite_true,ite_false,Nat.reduceLT,ite_eq_right (by decide : ¬ (8:Nat)=16)]
    · by_cases he16 : i=16
      · subst i; simp only [ite_true,ite_false,Nat.reduceLT,ite_eq_right (by decide : ¬ (16:Nat)=8)]
      · simp only [h8,he8,he16,ite_false]
        rw [ite_eq_left (by omega)]

/-- Initializes the mask seed in the second lane while preserving the
commitment state in every first lane. -/
theorem upperInit_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<8, InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block upperInit) s fun t =>
      RegKeep [.x7,.x8] s t ∧ t.mem=s.mem ∧
      Pairs t A (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) := by
  change WP isa (.block (((List.range 8).flatMap fun i =>
    ([.ldr .x .x7 .x4 (8*i),.vop (.ins .d2 (vreg i) 1 .x7)] : List Instr)) ++
    ([.movz .x .x7 0 0] ++
    ((List.range 17).map fun i => .vop (.ins .d2 (vreg (8+i)) 1 .x7)) ++ upperFinish))) s _
  rw [WP.block_append_iff]
  refine WP.mono (upperWords_ok hp hin) fun a ⟨ha,hma,hpa⟩ => ?_
  change WP isa (.block (.movz .x .x7 0 0 ::
    (((List.range 17).map fun i => .vop (.ins .d2 (vreg (8+i)) 1 .x7)) ++ upperFinish))) a _
  refine wp_movz fun b hb => ?_
  have hpb : Pairs b A (seedPrefix B s.mem (s.gpr .x4) 8) := by
    intro i hi; rw [hb.vec]; exact hpa i hi
  rw [WP.block_append_iff]
  refine WP.mono (clearHigh_ok hpb (by rw [hb.gpr]; rfl)) fun c ⟨hc,hmc,hpc⟩ => ?_
  refine WP.mono (upperFinish_ok hpc) fun t ⟨ht,hmt,hpt⟩ => ?_
  have h5 : c.gpr .x5=s.gpr .x5 :=
    (hc.gpr .x5 (by simp)).trans ((hb.other .x5 (by decide)).trans (ha.gpr .x5 (by decide)))
  rw [h5,seedNonceState_eq] at hpt
  exact ⟨(((ha.trans (RegKeep.upd hb)).trans hc).trans ht).mono (by simp),
    hmt.trans (hmc.trans (hb.mem.trans hma)),hpt⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailInitial.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (low Lanes)
open VG.Proof.Sha3.AArch64 (WP.cons)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def upperState (s : State) : Spec.Sha3.State :=
  Vector.ofFn fun i => vdword (s.v (vreg i.val)) 1

theorem lanes_pairs {s : State} {A : Spec.Sha3.State} (hp : Lanes s A) :
    Pairs s A (upperState s) := by
  intro i hi
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq _ hi]
  simp only [upperState,Vector.getElem_ofFn]
  apply vec64_ext
  · rw [vdword_ofVDwords_0]
    exact hp i hi
  · rw [vdword_ofVDwords_1]

/-- Both independent SHAKE streams are initialized, with the next
commitment-rate block pointer positioned immediately after the first. -/
theorem initial_ok {s : State}
    (hmu : ∀j<4, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀j<4, InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*j)) 16)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x1+64) 8)
    (hseed : ∀j<8, InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block (first++upperInit++([.addImm .x .x5 .x1 72] : List Instr))) s fun t =>
      RegKeep [.x5,.x6,.x7,.x8] s t ∧ t.mem=s.mem ∧ t.gpr .x5=s.gpr .x1+72 ∧
      Pairs t (firstState s.mem (s.gpr .x0) (s.gpr .x1))
        (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (first_ok hmu hw hl) fun a ⟨ha,hma,hpa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (upperInit_ok (lanes_pairs hpa) ?_) fun b ⟨hb,hmb,hpb⟩ => ?_
  · intro j hj
    rw [ha.rd,ha.wr,ha.gpr .x4 (by decide)]
    exact hseed j hj
  · rw [hma,ha.gpr .x4 (by decide),ha.gpr .x5 (by decide)] at hpb
    refine WP.cons rfl (WP.block_nil_iff.mpr ?_)
    refine ⟨?_,hmb.trans hma,?_,hpb⟩
    · refine ⟨fun r hr => ?_,hb.rd.trans ha.rd,hb.wr.trans ha.wr,hb.sp.trans ha.sp⟩
      have h5 : r≠.x5 := fun he => hr (by simp [he])
      simp only [RegUpd.gpr_write,h5,ite_false]
      exact (hb.gpr r (fun hh => hr (by simp_all))).trans
        (ha.gpr r (fun hh => hr (by simp_all)))
    · simp only [RegUpd.gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq]
      rw [hb.gpr .x1 (by decide),ha.gpr .x1 (by decide)]
      rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end
