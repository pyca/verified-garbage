module

import VerifiedGarbage.Proof.Bignum.X86.CrtAcceptance
public import VerifiedGarbage.Proof.Bignum.X86.CrtValidationFrame
public import VerifiedGarbage.Impl.Bignum.X86.CrtCore
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Bignum.X86.CheckFactorProduct
import VerifiedGarbage.Proof.Bignum.X86.CrtProductLayout
import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # The private CRT acceptance mask exactly implements the shared key and input checks -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt VG.Proof.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validate_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes)
    (modulus : wordsVal s.mem base (slot n modulusSlot) n = wordsVal s.mem base (slot n modulusSlot) (2 * n)) :
    WP isa (validate n) s fun t =>
      t.mem.readW (off base acceptanceOffset) 32 = mask32
        ((wordsVal s.mem base (slot n pSlot) n * wordsVal s.mem base (slot n qSlot) n =
          wordsVal s.mem base (slot n modulusSlot) n) ∧
          wordsVal s.mem base (slot n inputSlot) n < wordsVal s.mem base (slot n modulusSlot) n ∧
          wordsVal s.mem base (slot n inverseSlot) n < wordsVal s.mem base (slot n pSlot) n) ∧
      Outs base (validationRanges n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have fit : size n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  have bound (i : Nat) (hi : i < 20) : slot n i + 16 * n ≤ bytes := by
    have H := slot_bound (n := n) hi
    unfold stride at H
    omega
  have header : 12 ≤ bytes := by have := size_eq n; omega
  have sep := VG.Proof.Mont.X86.Dynamic.slot_le (n := n) (i := modulusSlot) (j := productSlot) (by decide)
  have head := VG.Proof.Mont.X86.Dynamic.slot_header n modulusSlot
  unfold validate
  refine WP.seq (WP.mono (checkFactorProduct_ok hs hn
    (product_layout hz (by decide) (by decide) (by decide) (by decide))
    (bound _ (by decide)) (by unfold stride at sep; omega) (by unfold multiplierOffset; omega))
    fun u ⟨Prod, O, K⟩ => ?_)
  have O₁ : Outs base (validationRanges n) s.mem u.mem := O.mono (by
    intro r hr
    simp only [validationRanges, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact hr.elim Or.inl (fun h => Or.inr (Or.inl h)))
  refine WP.seq (WP.mono (storeMask_ok (hs.of_keeps K (by decide)) header) fun v ⟨Saved, Ov, Kv⟩ => ?_)
  have O₂ : Outs base (validationRanges n) s.mem v.mem := O₁.trans (Outs.of_outside Ov (by simp [validationRanges]))
  have K₂ := K.trans (Kv.mono (by decide))
  refine WP.seq (WP.mono (lessThan_ok n (hs.of_keeps K₂ (by decide)) hn
    (by have := bound inputSlot (by decide); omega) (by have := bound modulusSlot (by decide); omega))
    fun w ⟨X, Kw, Mw⟩ => ?_)
  have K₃ := K₂.trans (Kw.mono (by decide))
  have SavedW : w.mem.readW (off base acceptanceOffset) 32 =
      mask32 (wordsVal s.mem base (slot n pSlot) n * wordsVal s.mem base (slot n qSlot) n =
        wordsVal s.mem base (slot n modulusSlot) n) := by rw [Mw, Saved, Prod, ← modulus]
  have XW := X
  rw [validation_value O₂ (by decide) (by omega) fit, validation_value O₂ (by decide) (by omega) fit] at XW
  refine WP.seq (WP.mono (mergeAcceptance_ok _ _ (hs.of_keeps K₃ (by decide)) header SavedW XW)
    fun x ⟨Sx, Ox, Kx⟩ => ?_)
  have O₃ : Outs base (validationRanges n) s.mem x.mem :=
    O₂.trans (by rw [← Mw]; exact Outs.of_outside Ox (by simp [validationRanges]))
  have K₄ := K₃.trans (Kx.mono (by decide))
  refine WP.seq (WP.mono (lessThan_ok n (hs.of_keeps K₄ (by decide)) hn
    (by have := bound inverseSlot (by decide); omega) (by have := bound pSlot (by decide); omega))
    fun y ⟨QI, Ky, My⟩ => ?_)
  have K₅ := K₄.trans (Ky.mono (by decide))
  have QIY := QI
  rw [validation_value O₃ (by decide) (by omega) fit, validation_value O₃ (by decide) (by omega) fit] at QIY
  have Sy := Sx
  rw [← My] at Sy
  refine WP.mono (mergeAcceptance_ok _ _ (hs.of_keeps K₅ (by decide)) header Sy QIY)
    fun t ⟨St, Ot, Kt⟩ => ?_
  exact ⟨by simpa only [and_assoc] using St,
    O₃.trans (by rw [← My]; exact Outs.of_outside Ot (by simp [validationRanges])), K₅.trans (Kt.mono (by decide))⟩

end VG.Proof.Bignum.X86.Crt
