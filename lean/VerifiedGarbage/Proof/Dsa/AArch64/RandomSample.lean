module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomRemaining

import VerifiedGarbage.Proof.Dsa.AArch64.RandomFunctional
import VerifiedGarbage.Proof.Dsa.AArch64.RandomNonceEncoding
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Entry and exit of the complete 128-draw sampler. -/
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
