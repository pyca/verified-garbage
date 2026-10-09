import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailWord

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop)

/-- Inserting one seed word into the second SHAKE stream preserves the
complete commitment state in the first lanes. -/
theorem upperWord_ok {s : State} {r : VReg} {off : Nat}
    (ho : off%8=0 ∧ off<4096*8)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 off) 8) :
    WP isa (.block [.ldr .x .x7 .x4 off,.vop (.ins .d2 r 1 .x7)]) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      (∀v,v≠r → t.v v=s.v v) ∧
      t.v r=setLane (s.v r) 64 1 (s.mem.readW (s.gpr .x4+BitVec.ofNat 64 off) 64) := by
  refine wp_ldr ho rfl hin fun a ha =>
    wp_vop (d:=r) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((RegKeep.upd ha).trans (RegKeep.vupd ht)).mono (by simp),
    ht.mem.trans ha.mem,?_,?_⟩
  · intro v hv
    rw [ht.get v hv,ha.vec]
  · rw [ht.v,ha.vec,ha.gpr]

/-- Both 64-bit lane values after a high-lane insert. -/
theorem upper_pair (a b w : BitVec 64) :
    setLane (ofVDwords a b) 64 1 w=ofVDwords a w := by
  apply vec64_ext
  · change (setLane (ofVDwords a b) 64 1 w).extractLsb' (64*0) 64=_
    rw [extract_setLane64 _ w (i:=1) (j:=0) (by decide) (by decide),
      vdword_ofVDwords_0]
    exact vdword_ofVDwords_0 a b
  · change (setLane (ofVDwords a b) 64 1 w).extractLsb' (64*1) 64=_
    rw [extract_setLane64 _ w (i:=1) (j:=1) (by decide) (by decide),vdword_ofVDwords_1]
    rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
