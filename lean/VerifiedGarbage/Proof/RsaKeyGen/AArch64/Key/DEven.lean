import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DBase
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath

/-!
# An RSA key from its primes on AArch64: `d` for an even `e`

`d = (e mod L)⁻¹ mod L` for an odd `L ≥ 3`, by `inverse` modulo `L` (or
3 otherwise) (`dEven_k`, `inverse_even`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

theorem dEven_mask_or (a b : Bool) : mask a ||| mask b = mask (a || b) := by cases a <;> cases b <;> decide

/-- `notMask`'s value. -/
theorem dEven_mask_not (c : Bool) : mask c ^^^ BitVec.setWidth 64 0#16 - 1#64 = mask (!c) := by cases c <;> decide

/-- The mask of `L` even or below 3 (`b`, the mask of `L < 3`, in `x15`)
into `x15`, its complement into `kOk`. -/
theorem dEvenMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {b : Bool} (h15 : s.gpr .x15 = mask b) :
    WP isa (.block (([mov .x10 .x15] : List Instr) ++ evenMaskOf aL ++
      ([.logic .orr .x .x15 .x15 .x10, mov .x10 .x15] : List Instr) ++ notMask ++
      ([sth .x15 kOk, mov .x15 .x10] : List Instr))) s fun t =>
      KS I s₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧
        word t.mem I.B (8 * kOk) = mask (!(decide (av I s.mem aL % 2 = 0) || b)) ∧
        t.gpr .x15 = mask (decide (av I s.mem aL % 2 = 0) || b) := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x10] (Q := fun t => t.gpr .x10 = mask b ∧ t.mem = s.mem) (by brun [h15])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h10, m₁⟩, k₁⟩ => ?_
  have h₁ := h.regs m₁ k₁
  rw [WP.block_append_iff]
  refine WP.mono (evenMaskOf_k h₁ (j := aL) (by decide)) fun s₂ ⟨h₂, m₂, h15₂, _, _, k₂⟩ => ?_
  rw [m₁] at h15₂
  have h10₂ : s₂.gpr .x10 = mask b := (k₂.gpr .x10 (by decide)).trans h10
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.x4, .x7, .x10, .x15] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
      (mask (!(decide (av I s.mem aL % 2 = 0) || b))) ∧ t.gpr .x15 = mask (decide (av I s.mem aL % 2 = 0) || b)) (by
    brun [notMask, h₂.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15₂, h10₂, dEven_mask_or,
      dEven_mask_not]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hm, h15t⟩, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k₃
  exact ⟨ht, by rw [m₁, ← m₂] at *; exact f₃, hw, h15t⟩

end VG.Proof.RsaKeyGen.AArch64.Key
