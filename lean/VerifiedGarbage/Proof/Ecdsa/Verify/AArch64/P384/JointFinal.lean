module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointPrep
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ProjectiveFlags
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass

def pointRanges : List (Nat×Nat) := genW ++ winX p384 ++ winW P384Joint.K ++ PubNaf.cacheW P384Joint.K

theorem point_bounds : ∀w∈pointRanges,w.1+w.2≤8192 := by decide

theorem point_fixed : FixedOk p384 pointRanges := by unfold FixedOk; decide

/-- The joint path preserves all flag/scalar inputs to the unchanged final check. -/
theorem finalState_of_joint {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
 (h : Mid p384 s₀ base g s) (hs : Scr t base size)
 (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hu : Unch base pointRanges s.mem t.mem)
 (hx : sv p384 base t RX<p384.C.p) (hz : sv p384 base t RZ<p384.C.p) :
 FinalState p384 s₀ base g t := by
 have same (i : Nat) (hi : i∈[RM',K]) : sv p384 base t i=sv p384 base s i := by
  apply hu.wordsVal
  · have he : ∀i∈[RM',K],∀w∈pointRanges,p384.sl i+48≤w.1 ∨ w.1+w.2≤p384.sl i := by decide
    exact he i hi
  · have he : ∀i∈[RM',K],p384.sl i+48≤2^64 := by decide
    exact he i hi
 refine ⟨hs,hw.trans h.wr,hr.trans h.rd,h.fixed.unch (by decide) h.scr.nowrap point_fixed hu,
  ?_,?_,?_,hz,?_,?_,hx⟩
 · rw [hu.word (by decide) (by decide)]
   exact h.flag
 · rw [same RM' (by simp)]; exact h.rm_lt
 · change toM _ _ (sv p384 base t RM')=_
   rw [same RM' (by simp)]; exact h.rm
 · exact unch_whole (h.unch.trans hu) (by
     intro w hw
     rcases List.mem_append.mp hw with hw|hw
     · rw [List.mem_singleton.mp hw]; exact Nat.le_refl _
     · exact point_bounds w hw)
 · rw [same K (by simp)]; exact h.k
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
