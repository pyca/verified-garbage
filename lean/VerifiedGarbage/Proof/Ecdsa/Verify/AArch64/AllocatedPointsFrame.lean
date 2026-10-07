import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedWindow
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointSetup
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyExtra

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

def bodyRanges : List (Nat × Nat) := jointPointRanges++[(7104,576)]
def pointRanges : List (Nat × Nat) := bodyRanges++[(7800,32)]

theorem point_bounds : ∀ w∈pointRanges,w.1+w.2≤size := by decide +kernel
theorem point_fixed : FixedOk p256 pointRanges := by unfold FixedOk; decide +kernel

theorem save_same {s t : State} {base : Addr}
    (hu : Outside base 7800 32 s.mem t.mem) :
    ∀ i<45,sv p256 base t i=sv p256 base s i := by
  intro i hi
  apply hu.unch.wordsVal
  · have h : ∀ i<45,∀ w∈[(7800,32)],p256.sl i+32≤w.1 ∨ w.1+w.2≤p256.sl i := by decide +kernel
    exact h i hi
  · have h : ∀ i<45,p256.sl i+32≤2^64 := by decide +kernel
    exact h i hi

/-- Saving extra registers touches no scalar, flag, peer or fixed verifier data. -/
theorem mid_saved {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid p256 s₀ base g s) (hk : KeepRegs [] s t)
    (hu : Outside base 7800 32 s.mem t.mem) (hsy : t.syms=s.syms) :
    Mid p256 s₀ base g t := by
  have same := save_same hu
  have whole : Unch base [(0,size)] s₀.mem t.mem := unch_whole (h.unch.trans hu.unch) (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
    · rw [List.mem_singleton.mp hw]; decide)
  refine ⟨h.scr.of_keepRegs hk (by simp),hk.wr.trans h.wr,hk.rd.trans h.rd,
    h.fixed.unch (by decide) h.scr.nowrap (by unfold FixedOk; decide +kernel) hu.unch,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,whole,hsy.trans h.syms,?_⟩
  · rw [same RX (by decide)]; exact h.rx
  · rw [same RY (by decide)]; exact h.ry
  · rw [same RZ (by decide)]; exact h.rz
  · rw [hu.unch.word (by decide +kernel) (by decide)]; exact h.flag
  · rw [same PX (by decide)]; exact h.px_lt
  · rw [same PY (by decide)]; exact h.py_lt
  · rw [same PX (by decide)]; exact h.px
  · rw [same PY (by decide)]; exact h.py
  · rw [same RM' (by decide)]; exact h.rm_lt
  · rw [same RM' (by decide)]; exact h.rm
  · rw [same U (by decide)]; exact h.u_lt
  · rw [same U (by decide)]; exact h.u
  · rw [same V (by decide)]; exact h.v_lt
  · rw [same V (by decide)]; exact h.v
  · rw [same VG.Impl.Ecdsa.AArch64.K (by decide)]; exact h.k

/-- The allocated body preserves the numerical inputs to the final check. -/
theorem finalState_of_allocated {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid p256 s₀ base g s) (hs : Scr t base size)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hu : Unch base pointRanges s.mem t.mem)
    (hx : sv p256 base t RX<p256.C.p) (hz : sv p256 base t RZ<p256.C.p) :
    FinalState p256 s₀ base g t := by
  have same (i : Nat) (hi : i∈[RM',VG.Impl.Ecdsa.AArch64.K]) : sv p256 base t i=sv p256 base s i := by
    apply hu.wordsVal
    · have he : ∀ i∈[RM',VG.Impl.Ecdsa.AArch64.K],∀ w∈pointRanges,p256.sl i+32≤w.1 ∨ w.1+w.2≤p256.sl i := by decide +kernel
      exact he i hi
    · have he : ∀ i∈[RM',VG.Impl.Ecdsa.AArch64.K],p256.sl i+32≤2^64 := by decide +kernel
      exact he i hi
  refine ⟨hs,hw.trans h.wr,hr.trans h.rd,h.fixed.unch (by decide) h.scr.nowrap point_fixed hu,
    ?_,?_,?_,hz,?_,?_,hx⟩
  · rw [hu.word (by decide +kernel) (by decide)]; exact h.flag
  · rw [same RM' (by simp)]; exact h.rm_lt
  · change toM _ _ (sv p256 base t RM')=_
    rw [same RM' (by simp)]; exact h.rm
  · exact unch_whole (h.unch.trans hu) (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
      · exact point_bounds w hw)
  · rw [same VG.Impl.Ecdsa.AArch64.K (by simp)]; exact h.k

end VG.Proof.Ecdsa.Verify.AArch64.Allocated
