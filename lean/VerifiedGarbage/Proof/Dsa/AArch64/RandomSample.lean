module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomRemaining

import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoop
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawResult
import VerifiedGarbage.Proof.Dsa.Encoding
/-! Entry and exit of the complete 128-draw sampler. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomFunctional.lean`, which only this module imported.
section

/-! Functional equivalence of the bounded sampling loop. -/
section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.Random

def RandomFunctionalInv (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample)
    (fuel : Nat) (s : State) : Prop :=
  0 < fuel ∧ fuel ≤ 128 ∧ ∃ used, RandomReady C used fuel s ∧
    word s.mem C.B Random.oStatus = 4 ∧ RandomResultRel C start result used fuel

private theorem functional_draw (C : RandomContext) (start : Nat) (result : Spec.Dsa.Random.Sample)
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes) (draws : Nat) (s : State)
    (hi : RandomFunctionalInv C start result draws s) :
    WP isa Random.draw s fun t => Scr t C.B Random.frameBytes ∧ t.sp = C.B ∧
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
    WP isa (.loop (.seq Random.draw (.block (Random.statusTest 4))) (.zero .x .x4)) s (RandomSamplePost C used (randomRemaining C used draws)) := by
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

end VG.Proof.Dsa.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomNonceEncoding.lean`, which only this module imported.
section

/-! Convert the right-aligned sampled scalar to the signer's nonce encoding. -/
section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

private theorem decode_padding (bs : List Byte) (n : Nat) :
    Spec.Dsa.decodeBE (List.replicate n 0 ++ bs) = Spec.Dsa.decodeBE bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, VG.Proof.Dsa.decodeBE_zero_cons]
    exact ih

theorem random_nonce_encoding {C : RandomContext} {used draws k : Nat} {s : State}
    (hr : RandomReady C used draws s) (hv : RandomNonceValue C k s) :
    Spec.Rsa.bytesAt s.mem (off C.B 200) C.qBytes.length = Spec.Dsa.encodeBE C.qBytes.length k := by
  obtain ⟨copied, hlen, hbytes, hdecode⟩ := hv
  let pad := C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1
  let padded := List.replicate pad (0 : Byte) ++ copied
  have hnfit := VG.Proof.Dsa.significant_fits C.qBytes
  have hpLen : padded.length = C.qBytes.length := by
    simp only [padded, List.length_append, List.length_replicate, hlen]
    exact Nat.sub_add_cancel hnfit
  have hpDec : Spec.Dsa.decodeBE padded = k := (decode_padding copied pad).trans hdecode
  have hpBytes : Spec.Rsa.bytesAt s.mem (off C.B 200) C.qBytes.length = padded := by
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, hpLen]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      have hil : i < C.qBytes.length := by simpa only [hpLen] using hj
      by_cases hip : i < pad
      · have he : off C.B 200 + BitVec.ofNat 64 i = off C.B (200 + i) := by
          simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
        rw [he, hr.padding i hip]
        simp only [padded, List.getElem_append_left (as := List.replicate pad (0 : Byte)) (bs := copied) (i := i) (by simpa only [List.length_replicate] using hip),
          List.getElem_replicate]
      · have htail : i - pad < copied.length := by rw [hlen]; omega
        have he : off C.B 200 + BitVec.ofNat 64 i =
            off C.B (200 + C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1) +
              BitVec.ofNat 64 (i - pad) := by
          simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
          congr 2
          dsimp only [pad]
          omega
        rw [he, hbytes (i - pad) htail]
        simp only [padded, List.getElem_append_right (as := List.replicate pad (0 : Byte)) (bs := copied) (i := i) (by simpa only [List.length_replicate] using Nat.le_of_not_lt hip),
          List.length_replicate]
  rw [hpBytes, ← hpLen, ← hpDec, VG.Proof.Dsa.encodeBE_decodeBE]

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.Random

theorem random_sample_init_ready {C : RandomContext} {used draws : Nat} {s t : State}
    (h : RandomReady C used draws s)
    (hm : t.mem = (s.mem.writeW (off C.B Random.oDraws) (128 : BitVec 64)).writeW
      (off C.B Random.oStatus) (4 : BitVec 64)) (hk : Keep [.x0, .x15] s t) :
    RandomReady C used 128 t ∧ word t.mem C.B Random.oStatus = 4 := by
  have hd := writeW_outside s.mem C.B (d := Random.oDraws) (128 : BitVec 64) (by decide)
  have hs := writeW_outside (s.mem.writeW (off C.B Random.oDraws) (128 : BitVec 64)) C.B
    (d := Random.oStatus) (4 : BitVec 64) (by decide)
  have hf : InScr C.B Random.frameBytes s.mem t.mem := by
    rw [hm]
    exact (InScr.of_outside hd (by decide)).trans (InScr.of_outside hs (by decide))
  have hw (d : Nat) (hd' : d + 8 ≤ 160 ∨ 168 ≤ d) (hs' : d + 8 ≤ 192) :
      word t.mem C.B d = word s.mem C.B d := by
    rw [hm, hs.word (Or.inl hs') (by omega), hd.word hd' (by omega)]
  refine ⟨⟨h.scr.congr hk.wr, hk.sp.trans h.sp,
    (hw _ (by decide) (by decide)).trans h.rand, (hw _ (by decide) (by decide)).trans h.randLen,
    (hw _ (by decide) (by decide)).trans h.usedWord, (hw _ (by decide) (by decide)).trans h.width,
    (hw _ (by decide) (by decide)).trans h.qLen, (hw _ (by decide) (by decide)).trans h.mask,
    (hw _ (by decide) (by decide)).trans h.q, ?_, h.randSrc.congrK hf hk, h.qSrc.congrK hf hk,
    h.usedBound, ?_, ?_⟩, ?_⟩
  · rw [hm, hs.word (by decide) (by decide), word_writeW_self]
    rfl
  · rw [hm]
    exact (h.frame.trans (Frm.of_outside (hd.mono (by decide) (by decide))
      (show (160, 72) ∈ randomWriteRanges by decide))).trans
      (Frm.of_outside (hs.mono (by decide) (by decide)) (show (160, 72) ∈ randomWriteRanges by decide))
  · intro i hi
    have ho : ofs C.B (off C.B (200 + i)) = 200 + i := by
      have he : off C.B (200 + i) + BitVec.ofNat 64 0 = off C.B (200 + i) := BitVec.add_zero _
      simpa only [he, Nat.add_zero] using ofs_off C.B (d := 200 + i) (i := 0) (by have := C.qlen; omega)
    rw [hm, hs _ (by rw [ho]; right; unfold Random.oStatus; omega),
      hd _ (by rw [ho]; right; unfold Random.oDraws; omega)]
    exact h.padding i hi
  · rw [hm, word_writeW_self]

theorem random_sample_correct {C : RandomContext} {used draws : Nat} {s : State}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes) (hr : RandomReady C used draws s) :
    WP isa Random.sample s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (sampleStatus (randomRemaining C used 128)) ∧
      RandomSamplePost C used (randomRemaining C used 128) t := by
  unfold Random.sample
  refine WP.seq (WP.mono (WP.keep [.x0, .x15] (Q := fun t =>
      t.mem = (s.mem.writeW (off C.B Random.oDraws) (128 : BitVec 64)).writeW
        (off C.B Random.oStatus) (4 : BitVec 64))
      (by unfold Random.store; brun [exec_addSp (show Random.oDraws < 4096 by decide),
        exec_addSp (show Random.oStatus < 4096 by decide), hr.sp, hr.scr.st (d := Random.oDraws) (by decide),
        hr.scr.st (d := Random.oStatus) (by decide)]
          rfl) rfl rfl rfl)
    fun a ⟨ham, hka⟩ => ?_)
  obtain ⟨har, has⟩ := random_sample_init_ready hr ham hka
  refine WP.seq (WP.mono (random_sampleLoop_correct hq har has (by decide) (by decide))
    fun b hb => ?_)
  obtain ⟨⟨draws', hbr⟩, hbs, hbv⟩ := hb
  refine WP.mono (WP.keep [.x0] (Q := fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (sampleStatus (randomRemaining C used 128)) ∧ t.mem = b.mem)
      (by brun [exec_ldrSp (show Random.oStatus % 8 = 0 ∧ Random.oStatus < 32768 by decide), hbr.sp, hbr.scr.ld (d := Random.oStatus) (by decide), hbs]) rfl rfl rfl)
    fun t ⟨⟨hta, htm⟩, hkt⟩ => ?_
  exact ⟨hta, ⟨draws', hbr.congr htm hkt⟩, by rw [htm]; exact hbs,
    fun k he => (hbv k he).congr htm⟩

/-- The complete sampler returns the specified status and byte consumption,
and a padded nonce suitable for the existing verified signer. -/
theorem random_sample_encoded {C : RandomContext} {used draws : Nat} {s : State}
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes) (hr : RandomReady C used draws s) :
    WP isa Random.sample s fun t =>
      let result := randomRemaining C used 128
      t.gpr .x0 = BitVec.ofNat 64 (sampleStatus result) ∧
      word t.mem C.B Random.oStatus = BitVec.ofNat 64 (sampleStatus result) ∧
      word t.mem C.B Random.oUsed = BitVec.ofNat 64 (used + result.used) ∧
      (∀ k, result.scalar = some k →
        Spec.Rsa.bytesAt t.mem (off C.B 200) C.qBytes.length = Spec.Dsa.encodeBE C.qBytes.length k) ∧
      Frm C.B randomWriteRanges C.initialMem t.mem ∧
      (∃ draws', RandomReady C (used + result.used) draws' t) ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x8, .x9, .x10, .x12, .x15] s t := by
  refine WP.mono (WP.keep [.x0, .x1, .x2, .x3, .x4, .x8, .x9, .x10, .x12, .x15]
    (random_sample_correct hq hr) (by rfl) rfl rfl) fun t ⟨⟨hta, ⟨draws', htr⟩, hstatus, htv⟩, hkt⟩ => ?_
  exact ⟨hta, hstatus, htr.usedWord, fun k hk => random_nonce_encoding htr (htv k hk), htr.frame,
    ⟨draws', htr⟩, hkt⟩

end VG.Proof.Dsa.AArch64
