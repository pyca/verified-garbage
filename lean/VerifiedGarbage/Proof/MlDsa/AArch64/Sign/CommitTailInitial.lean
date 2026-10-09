import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailUpperInit

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
