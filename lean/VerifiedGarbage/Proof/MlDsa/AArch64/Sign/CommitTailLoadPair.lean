import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailAbsorb

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_ldrq wp_vop)
open VG.Proof.Sha3.AArch64.Sha3.Vector (low low_ext8)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Loads two consecutive words into consecutive low lanes; the temporary
high-lane values are overwritten by the independent mask initialization. -/
theorem loadPair_ok {s : State} {j off : Nat} {r : Reg}
    (hj : j+1<25) (ho : off%16=0 ∧ off<4096*16)
    (hin : InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 off) 16) :
    WP isa (.block [.ldrq (vreg j) r off,
      .vop (.ext (vreg (j+1)) (vreg j) (vreg j) 8)]) s fun t =>
      RegKeep [] s t ∧ t.mem=s.mem ∧ ∀i<25,
      low t (vreg i)= if i=j+1 then (s.mem.read (s.gpr r+BitVec.ofNat 64 off) 16).extractLsb' 64 64
        else if i=j then (s.mem.read (s.gpr r+BitVec.ofNat 64 off) 16).extractLsb' 0 64
        else low s (vreg i) := by
  refine wp_ldrq ho rfl hin fun a ha =>
    wp_vop (d:=vreg (j+1)) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((RegKeep.vupd ha).trans (RegKeep.vupd ht)).mono (by simp),ht.mem.trans ha.mem,?_⟩
  intro i hi
  by_cases he : i=j+1
  · subst i
    simp only [ite_true,low,ht.v,ha.v]
    exact low_ext8 _
  · have he' : vreg i≠vreg (j+1) := by
      rw [ne_eq,vreg_inj i (by omega) (j+1) (by omega)]; exact he
    simp only [he,ite_false,low,ht.get _ he']
    by_cases he0 : i=j
    · subst i
      simp only [ite_true,ha.v]
      rfl
    · have he0' : vreg i≠vreg j := by
        rw [ne_eq,vreg_inj i (by omega) j (by omega)]; exact he0
      rw [ite_eq_right he0,ha.get _ he0']

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
