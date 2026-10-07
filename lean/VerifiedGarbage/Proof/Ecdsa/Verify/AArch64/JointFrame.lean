import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.FinalState
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPrep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

/-- The points stage writes only arithmetic work, public digits, and precomputation. -/
def jointPointRanges : List (Nat×Nat) :=
  [(128,32),(512,544),(1504,584),(2848,1536),(5400,64),(6000,512)]

theorem jointPoint_fixed : FixedOk p256 jointPointRanges := by unfold FixedOk; decide +kernel

theorem jointPoint_bounds : ∀ w∈jointPointRanges,w.1+w.2≤size := by decide +kernel

theorem jointPoint_prep : ∀ w∈jointPrepRanges,∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_table : ∀ w∈jacTreeWrites P256Joint.cfg.K,∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_cache : ∀ w∈CachedInit.outputs.map (·,32)++[(128,32)],∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_loop : ∀ w∈(jointWork P256Joint.cfg).map (·,32)++[(128,32)],∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_finish : ∀ w∈jacLoopWrites P256Joint.cfg.K,∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_union {base : Addr} {a b c : Mem}
    (h : Unch base jointPointRanges a b) (h' : Unch base jointPointRanges b c) :
    Unch base jointPointRanges a c :=
  (h.trans h').mono fun _ hw => (List.mem_append.mp hw).elim id id

/-- The point calculation preserves every scalar and flag needed by the final check. -/
theorem finalState_of_joint {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid p256 s₀ base g s) (hs : Scr t base size)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr)
    (hu : Unch base jointPointRanges s.mem t.mem)
    (hx : sv p256 base t RX<p256.C.p) (hz : sv p256 base t RZ<p256.C.p) :
    FinalState p256 s₀ base g t := by
  have same (i : Nat) (hi : i∈[RM',K]) : sv p256 base t i=sv p256 base s i := by
    apply hu.wordsVal
    · have he : ∀ i∈[RM',K],∀ w∈jointPointRanges,p256.sl i+32≤w.1 ∨ w.1+w.2≤p256.sl i := by decide +kernel
      exact he i hi
    · have he : ∀ i∈[RM',K],p256.sl i+32≤2^64 := by decide +kernel
      exact he i hi
  refine ⟨hs,hw.trans h.wr,hr.trans h.rd,h.fixed.unch (by decide) h.scr.nowrap jointPoint_fixed hu,
    ?_,?_,?_,hz,?_,?_,hx⟩
  · rw [hu.word (by decide +kernel) (by decide)]
    exact h.flag
  · rw [same RM' (by simp)]; exact h.rm_lt
  · change toM _ _ (sv p256 base t RM')=_
    rw [same RM' (by simp)]; exact h.rm
  · exact unch_whole (h.unch.trans hu) (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
      · exact jointPoint_bounds w hw)
  · rw [same K (by simp)]; exact h.k

end VG.Proof.Ecdsa.Verify.AArch64
