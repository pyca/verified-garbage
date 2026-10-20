module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomRemaining
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
import VerifiedGarbage.Proof.Framework.Omega

/-! Functional equivalence of the bounded sampling loop. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64 VG.Proof.Dsa.Random

def RandomFunctionalInv (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample)
    (fuel : Nat) (s : State) : Prop :=
  0 < fuel ∧ fuel ≤ 128 ∧ ∃ used, RandomReady C used fuel s ∧
    word s.mem C.B Random.oStatus = 4 ∧ RandomResultRel C start result used fuel

private theorem functional_draw (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample)
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes) (draws : Nat) (s : State)
    (hi : RandomFunctionalInv C start result draws s) :
    WP isa Random.draw s fun t => Scr t C.B Random.frameBytes ∧ t.gpr .rsp = C.B ∧
      ((word t.mem C.B Random.oStatus ≠ 4 ∧ RandomSamplePost C start result t) ∨
       (word t.mem C.B Random.oStatus = 4 ∧ ∃ k < draws, RandomFunctionalInv C start result k t)) := by
  obtain ⟨hdpos, hdbound, used, hr, hstatus, hrel⟩ := hi
  cases draws with
  | zero => omega
  | succ fuel =>
    let n := (VG.Proof.Dsa.significant C.qBytes).1
    have hnfit : n ≤ C.qBytes.length := VG.Proof.Dsa.significant_fits C.qBytes
    by_cases hfull : used + n ≤ C.rand.length
    · refine WP.mono (random_draw_full_result hr hstatus hfull (by omega) (by omega))
        fun t ⟨htr, hts, htv⟩ => ?_
      refine ⟨htr.scr, htr.sp, ?_⟩
      by_cases ha : 0 < randomNextCandidate C used ∧ randomNextCandidate C used < Spec.Dsa.decodeBE C.qBytes
      · rw [decide_eq_true ha, ite_eq_left rfl] at htr hts
        have he := random_remaining_accept hq hfull ha (fuel := fuel)
        have hscalar : result.scalar = some (randomNextCandidate C used) := by rw [hrel.scalar, he]
        have hused : start + result.used = used + n := by
          have h := hrel.consumption
          rw [he] at h
          exact h
        have hst : sampleStatus result = 1 := by rw [hrel.status, he]; rfl
        refine Or.inl ⟨by rw [hts]; decide, ⟨fuel + 1, ?_⟩, ?_, ?_⟩
        · rw [hused]; exact htr
        · rw [hst]; exact hts
        · intro k hk
          rw [hscalar] at hk
          cases hk
          exact htv
      · simp only [ha, decide_false, Bool.false_eq_true, ite_false] at htr hts
        have hnext := hrel.reject hq hfull ha
        cases fuel with
        | zero =>
          have hscalar : result.scalar = none := hnext.scalar
          have hused : start + result.used = used + n := by
            have h := hnext.consumption
            simpa only [randomRemaining, Spec.Dsa.Random.sample, Nat.add_zero] using h
          have hst : sampleStatus result = 0 := hnext.status
          have hzero : word t.mem C.B Random.oStatus = 0 := by simpa only [ite_true] using hts
          refine Or.inl ⟨by rw [hzero]; decide, ⟨0, ?_⟩, ?_, ?_⟩
          · rw [hused]; exact htr
          · rw [hst]; exact hzero
          · intro k hk
            rw [hscalar] at hk
            cases hk
        | succ f =>
          have hfour : word t.mem C.B Random.oStatus = 4 := by
            rw [hts, ite_eq_right (by omega)]
          exact Or.inr ⟨hfour, f + 1, by omega, by omega, by omega,
            used + n, htr, hfour, hnext⟩
    · have hshort : C.rand.length - used < n := by have := hr.usedBound; omega
      refine WP.mono (random_draw_short_ok hr.scr hr.sp hr.randLen hr.usedWord hr.width hr.usedBound
        C.randBound (by have := C.qlen; omega) hshort) fun t ⟨_, htm, hkt⟩ => ?_
      have htr := hr.after_status htm hkt
      have he := random_remaining_short hq hshort (fuel := fuel)
      have hscalar : result.scalar = none := by rw [hrel.scalar, he]
      have hused : start + result.used = used := by
        have h := hrel.consumption
        rw [he] at h
        simpa only [Nat.add_zero] using h
      have hst : sampleStatus result = 2 := by rw [hrel.status, he]; rfl
      have htwo : word t.mem C.B Random.oStatus = 2 := by rw [htm, word_writeW_self]
      refine ⟨htr.scr, htr.sp, Or.inl ⟨by rw [htwo]; decide, ⟨fuel + 1, ?_⟩, ?_, ?_⟩⟩
      · rw [hused]; exact htr
      · rw [hst]; exact htwo
      · intro k hk
        rw [hscalar] at hk
        cases hk

theorem random_sampleLoop_correct {C : RandomContext} {used draws : Nat} {s : State}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes) (hr : RandomReady C used draws s)
    (hstatus : word s.mem C.B Random.oStatus = 4) (hdpos : 0 < draws) (hdbound : draws ≤ 128) :
    WP isa (.loop (.seq Random.draw (.block [.mov .rax (.mem (Random.sp Random.oStatus)),
      .alu .cmp .rax (.imm 4)])) .e) s (RandomSamplePost C used (randomRemaining C used draws)) := by
  refine random_sampleLoop_rule C.B (RandomFunctionalInv C used (randomRemaining C used draws))
    (RandomSamplePost C used (randomRemaining C used draws)) ?_ ?_
    (functional_draw C used (randomRemaining C used draws) hq)
    (n := draws) ⟨hdpos, hdbound, used, hr, hstatus, rfl, rfl, rfl⟩
  · intro n a b hi hm hk
    obtain ⟨hp, hb, used', hr', hs', hrel⟩ := hi
    exact ⟨hp, hb, used', hr'.congr hm hk, by rw [hm]; exact hs', hrel⟩
  · intro a b hi hm hk
    obtain ⟨⟨draws', hr'⟩, hs', hv⟩ := hi
    exact ⟨⟨draws', hr'.congr hm hk⟩, by rw [hm]; exact hs', fun k he => (hv k he).congr hm⟩

end VG.Proof.Dsa.X86_64
