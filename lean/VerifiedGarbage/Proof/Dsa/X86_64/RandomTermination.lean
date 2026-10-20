module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw

/-! Memory-safe termination of the actual bounded sampling loop. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def RandomLoopInv (C : RandomContext) (draws : Nat) (s : State) : Prop :=
  0 < draws ∧ draws ≤ 128 ∧ ∃ used, RandomReady C used draws s ∧ word s.mem C.B Random.oStatus = 4

def RandomLoopExit (C : RandomContext) (s : State) : Prop :=
  ∃ used draws, RandomReady C used draws s ∧ word s.mem C.B Random.oStatus ≠ 4

theorem random_draw_progress (C : RandomContext) (draws : Nat) (s : State)
    (hi : RandomLoopInv C draws s) :
    WP isa Random.draw s fun t => Scr t C.B Random.frameBytes ∧ t.gpr .rsp = C.B ∧
      ((word t.mem C.B Random.oStatus ≠ 4 ∧ RandomLoopExit C t) ∨
       (word t.mem C.B Random.oStatus = 4 ∧ ∃ k < draws, RandomLoopInv C k t)) := by
  obtain ⟨hdpos, hdbound, used, hr, hstatus⟩ := hi
  let n := (VG.Proof.Dsa.significant C.qBytes).1
  have hnfit : n ≤ C.qBytes.length := VG.Proof.Dsa.significant_fits C.qBytes
  by_cases hfull : used + n ≤ C.rand.length
  · refine WP.mono (random_draw_full_ok hr.scr hr.sp hr.rand hr.randLen hr.usedWord hr.width
      hr.qLen hr.mask hr.q hr.draws hr.randSrc hr.qSrc C.qlen C.randBound C.positive hfull
      hdpos (by omega)) fun t ⟨m, copied, hclen, _, _, hcopy, htm, hkt⟩ => ?_
    let accepted := decide (0 < Spec.Dsa.decodeBE copied ∧ Spec.Dsa.decodeBE copied < Spec.Dsa.decodeBE C.qBytes)
    have htm' : t.mem = randomDrawFinishMem
        (m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + n))) C.B accepted draws := by
      rw [htm, hclen]
    have htready := hr.after_draw accepted hfull hcopy htm' hkt
    have htstatus : word t.mem C.B Random.oStatus =
        if accepted then 1 else if draws = 1 then 0 else 4 := by
      rw [htm', random_drawFinish_status]
      have he : word (m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + n))) C.B Random.oStatus = 4 := by
        rw [(writeW_outside _ C.B _ (by decide)).word (by decide) (by decide),
          (hcopy.mono (o' := 200) (n' := 32) (by have := VG.Proof.Dsa.significant_fits C.qBytes; omega) (by have := C.qlen; have := VG.Proof.Dsa.significant_fits C.qBytes; omega)).word (by decide) (by decide)]
        exact hstatus
      rw [he]
    refine ⟨htready.scr, htready.sp, ?_⟩
    cases ha : accepted with
    | true =>
      have hne : word t.mem C.B Random.oStatus ≠ 4 := by rw [htstatus, ha, ite_eq_left rfl]; decide
      exact Or.inl ⟨hne, used + n, _, htready, hne⟩
    | false =>
      by_cases hd1 : draws = 1
      · have hne : word t.mem C.B Random.oStatus ≠ 4 := by rw [htstatus, ha, ite_eq_left hd1]; decide
        exact Or.inl ⟨hne, used + n, _, htready, hne⟩
      · have hfour : word t.mem C.B Random.oStatus = 4 := by rw [htstatus, ha, ite_eq_right hd1]; rfl
        refine Or.inr ⟨hfour, draws - 1, by omega, by omega, by omega, used + n, ?_, hfour⟩
        simpa only [ha, Bool.false_eq_true, ite_false] using htready
  · have hshort : C.rand.length - used < n := by have := hr.usedBound; omega
    refine WP.mono (random_draw_short_ok hr.scr hr.sp hr.randLen hr.usedWord hr.width hr.usedBound
      C.randBound (by have := C.qlen; omega) hshort) fun t ⟨_, htm, hkt⟩ => ?_
    have htready := hr.after_status htm hkt
    have hne : word t.mem C.B Random.oStatus ≠ 4 := by rw [htm, word_writeW_self]; decide
    exact ⟨htready.scr, htready.sp, Or.inl ⟨hne, used, draws, htready, hne⟩⟩

/-- Every iteration either exits or decreases the positive draw budget. -/
theorem random_sampleLoop_terminates {C : RandomContext} {draws : Nat} {s : State}
    (hi : RandomLoopInv C draws s) :
    WP isa (.loop (.seq Random.draw (.block [.mov .rax (.mem (Random.sp Random.oStatus)),
      .alu .cmp .rax (.imm 4)])) .e) s (RandomLoopExit C) := by
  refine random_sampleLoop_rule C.B (RandomLoopInv C) (RandomLoopExit C) ?_ ?_
    (random_draw_progress C) hi
  · intro n s t hs hm hk
    obtain ⟨hp, hb, used, hr, hstatus⟩ := hs
    exact ⟨hp, hb, used, hr.congr hm hk, by rw [hm]; exact hstatus⟩
  · intro s t hs hm hk
    obtain ⟨used, draws, hr, hstatus⟩ := hs
    exact ⟨used, draws, hr.congr hm hk, by rw [hm]; exact hstatus⟩

end VG.Proof.Dsa.X86_64
