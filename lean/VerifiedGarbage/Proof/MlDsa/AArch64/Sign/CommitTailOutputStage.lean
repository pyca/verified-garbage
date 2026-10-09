import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailOutputBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailFront

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_mov WP.cons)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.MlKem.AArch64 (mov)

def outputStage (olen : Nat) : List Instr :=
  [mov .x2 .x21]++output olen++[.addImm .x .x0 .x19 256,mov .x4 .x20]

theorem outputStage_ok {s : State} {A B : Spec.Sha3.State} {n : Nat}
    (hn : n≤12) (hp : Pairs s A B)
    (hout : ∀i<n,InRegions s.wr (s.gpr .x21+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (outputStage (16*n))) s fun t =>
      RegKeep [.x0,.x2,.x4] s t ∧ Frame [⟨s.gpr .x21,16*n⟩] s.mem t.mem ∧
      t.gpr .x0=s.gpr .x19+256 ∧ t.gpr .x4=s.gpr .x20 ∧
      Spec.Sha3.bytesAt t.mem (s.gpr .x21) (16*n)=(Spec.Sha3.toBytes A).take (16*n) := by
  unfold outputStage
  rw [List.append_assoc,WP.block_append_iff]
  refine wp_mov fun a ha => WP.block_nil_iff.mpr ?_
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (s:=a) (A:=A) (B:=B) (p:=s.gpr .x21) n hn (by intro i hi; rw [ha.vec]; exact hp i hi)
    ha.gpr (by intro i hi; rw [ha.wr]; exact hout i hi)) fun b ⟨hb,hpb,hbytes,hf⟩ => ?_
  have hfb : Frame [⟨s.gpr .x21,16*n⟩] s.mem b.mem := by simpa only [ha.mem] using hf
  refine WP.cons rfl (wp_mov fun t ht => WP.block_nil_iff.mpr ?_)
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine ⟨fun r hr => ?_,ht.rd.trans hb.rd |>.trans ha.rd,
      ht.wr.trans hb.wr |>.trans ha.wr,ht.sp.trans hb.sp |>.trans ha.sp⟩
    have h4 : r≠.x4 := fun e => hr (by simp [e])
    have h0 : r≠.x0 := fun e => hr (by simp [e])
    rw [ht.other r h4,RegUpd.gpr_write,ite_eq_right h0,hb.gpr r (by simp),ha.other r (by
      intro e; apply hr; simp [e])]
  · rw [ht.mem]; exact hfb
  · rw [ht.other .x0 (by decide),RegUpd.gpr_write_self]
    change b.gpr .x19+256=s.gpr .x19+256
    rw [hb.gpr .x19 (by simp),ha.other .x19 (by decide)]
  · rw [ht.gpr,RegUpd.gpr_write,ite_eq_right (by decide : ¬ Reg.x20=Reg.x0),
      hb.gpr .x20 (by simp),ha.other .x20 (by decide)]
  · rw [ht.mem]
    exact ratePairs_bytes hbytes hn

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
