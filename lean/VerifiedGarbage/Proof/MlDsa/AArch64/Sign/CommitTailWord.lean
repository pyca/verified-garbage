import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CommitTail
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

private theorem low_zero (w : BitVec 64) : setLane 0 64 0 w=ofVDwords w 0 := by
  apply vec64_ext
  · change (setLane 0 64 0 w).extractLsb' (64*0) 64=_
    rw [extract_setLane64 0 w (i := 0) (j := 0) (by decide) (by decide),vdword_ofVDwords_0]
    rfl
  · change (setLane 0 64 0 w).extractLsb' (64*1) 64=_
    rw [extract_setLane64 0 w (i := 0) (j := 1) (by decide) (by decide),vdword_ofVDwords_1]
    rfl

/-- A commitment absorb changes only the low lane. The independent mask
stream in the high lane remains intact across every block. -/
theorem lowWord_ok {s : State} {r : VReg} {off : Nat}
    (hr : r≠.v25) (ho : off%8=0 ∧ off<4096*8)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 off) 8) :
    WP isa (.block (lowWord r off)) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      (∀v,v≠r → v≠.v25 → t.v v=s.v v) ∧
      t.v r=s.v r ^^^ ofVDwords (s.mem.readW (s.gpr .x5+BitVec.ofNat 64 off) 64) 0 := by
  unfold lowWord
  refine wp_ldr ho rfl hin fun a ha =>
    wp_vop (d := .v25) rfl fun b hb =>
    wp_vop (d := .v25) rfl fun c hc =>
    wp_vop (d := r) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((((RegKeep.upd ha).trans (RegKeep.vupd hb)).trans (RegKeep.vupd hc)).trans
    (RegKeep.vupd ht)).mono (by simp),ht.mem.trans (hc.mem.trans (hb.mem.trans ha.mem)),?_,?_⟩
  · intro v hvr hv25
    rw [ht.get v hvr,hc.get v hv25,hb.get v hv25,ha.vec]
  · rw [ht.v,hc.get r hr,hb.get r hr,ha.vec,hc.v,hb.v,hb.gpr,ha.gpr]
    exact congrArg (fun x => s.v r ^^^ x) (low_zero _)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
