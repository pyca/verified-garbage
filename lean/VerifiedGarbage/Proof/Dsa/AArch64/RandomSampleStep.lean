module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSamplePublic
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.RandomEncoding

/-! A draw's public status and the trace suffix retained after rejection. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomSampleStepStatus (p : RandomSamplePublic) : Nat :=
  if p.draw.used + p.draw.width ≤ p.draw.randLen then
    if p.accept then 1 else if p.draw.draws = 1 then 0 else 4
  else 2

def RandomSampleStepPost (p : RandomSamplePublic) (s : State) : Prop :=
  Scr s p.draw.B Random.frameBytes ∧ s.sp = p.draw.B ∧
  word s.mem p.draw.B Random.oStatus = BitVec.ofNat 64 (randomSampleStepStatus p) ∧
  ∀ (hfull : p.draw.used + p.draw.width ≤ p.draw.randLen) (hf : 1 < p.draw.draws),
    p.accept = false → RandomSampleTracePre (p.next hfull hf) s

theorem random_sample_step {p : RandomSamplePublic} {s : State} (h : RandomSampleTracePre p s) :
    WP isa Random.draw s (RandomSampleStepPost p) := by
  obtain ⟨rand, hlen, m, hr, hs, ht⟩ := h
  have hwidth := VG.Proof.Dsa.significant_fits p.draw.qBytes
  have hqlen := p.draw.qlen
  by_cases hfull : p.draw.used + p.draw.width ≤ p.draw.randLen
  · have hacc : randomDrawAccept p.draw rand = p.accept := by
      have hh := VG.Proof.Dsa.Random.sample_trace_head (Spec.Dsa.decodeBE p.draw.qBytes) (p.draw.draws - 1)
        (rand.drop p.draw.used) p.valid (by
          rw [VG.Proof.Dsa.random_drawBytes_scan, List.length_drop, hlen]
          exact Nat.le_sub_of_add_le' hfull)
      rw [show p.draw.draws - 1 + 1 = p.draw.draws by have := p.draw.drawsPos; omega, ht,
        VG.Proof.Dsa.random_drawBytes_scan] at hh
      exact hh.symm
    refine WP.mono (random_draw_full_result hr hs
      (by dsimp only [RandomDrawPublic.context]; rw [hlen]; exact hfull) p.draw.drawsPos p.draw.drawsBound)
      fun t ⟨htr, hstatus, _⟩ => ?_
    change RandomReady (p.draw.context rand hlen m) (p.draw.used + p.draw.width)
      (if randomDrawAccept p.draw rand then p.draw.draws else p.draw.draws - 1) t at htr
    change word t.mem p.draw.B Random.oStatus =
      (if randomDrawAccept p.draw rand then 1 else if p.draw.draws = 1 then 0 else 4) at hstatus
    rw [hacc] at htr hstatus
    refine ⟨htr.scr, htr.sp, ?_, ?_⟩
    · unfold randomSampleStepStatus
      rw [ite_eq_left hfull]
      cases ha : p.accept <;> by_cases hf : p.draw.draws = 1 <;>
        simp only [ha, hf, ite_true, ite_false, Bool.false_eq_true] at hstatus ⊢ <;> exact hstatus
    · intro hf hn ha
      simp only [ha, Bool.false_eq_true, ite_false] at htr
      refine ⟨rand, hlen, m, htr, ?_, ?_⟩
      · change word t.mem p.draw.B Random.oStatus = 4
        rw [ha, ite_eq_right (by decide), ite_eq_right (by omega : p.draw.draws ≠ 1)] at hstatus
        exact hstatus
      · exact random_sample_trace_next hlen ht hf hn ha
  · have hshort : (p.draw.context rand hlen m).rand.length - p.draw.used <
        (VG.Proof.Dsa.significant (p.draw.context rand hlen m).qBytes).1 := by
      dsimp only [RandomDrawPublic.context]
      rw [hlen]
      have := p.draw.usedBound
      unfold RandomDrawPublic.width at hfull
      omega
    refine WP.mono (random_draw_short_ok hr.scr hr.sp hr.randLen hr.usedWord hr.width hr.usedBound
      (p.draw.context rand hlen m).randBound (by dsimp only [RandomDrawPublic.context]; omega) hshort)
      fun t ⟨_, hm, hk⟩ => ?_
    have htr := hr.after_status hm hk
    refine ⟨htr.scr, htr.sp, ?_, fun hf _ _ => False.elim (hfull hf)⟩
    rw [hm]
    change word (s.mem.writeW (off p.draw.B Random.oStatus) (2 : BitVec 64)) p.draw.B Random.oStatus = _
    rw [word_writeW_self, randomSampleStepStatus, ite_eq_right hfull]
    rfl

theorem RandomSampleStepPost.congr {p : RandomSamplePublic} {s t : State}
    (h : RandomSampleStepPost p s) (hm : t.mem = s.mem) (hk : Keep [.x0, .x4] s t) :
    RandomSampleStepPost p t :=
  ⟨h.1.congr hk.wr, hk.sp.trans h.2.1, by rw [hm]; exact h.2.2.1,
    fun hf hn ha => (h.2.2.2 hf hn ha).congr hm hk⟩

theorem random_sample_status_four {p : RandomSamplePublic} (h : randomSampleStepStatus p = 4) :
    p.draw.used + p.draw.width ≤ p.draw.randLen ∧ 1 < p.draw.draws ∧ p.accept = false := by
  unfold randomSampleStepStatus at h
  split at h
  next hf =>
    cases ha : p.accept <;> simp only [ha, Bool.false_eq_true, ite_true, ite_false] at h
    · have hp := p.draw.drawsPos
      by_cases hn : p.draw.draws = 1
      · rw [ite_eq_left hn] at h; contradiction
      · exact ⟨hf, by omega, rfl⟩
    · contradiction
  next => contradiction

end VG.Proof.Dsa.AArch64
