module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
import VerifiedGarbage.Proof.Framework.Omega

/-! Preserve the prepared modulus across witness selection and shared rounds. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.MlKem.AArch64

def modulusArrays : List Nat := [aN, aOne, aR2, aR1, aRm1]

theorem ModulusReady.of_frm {s t : State} {B : Addr} {Z w N : Nat}
    {rs : List (Nat × Nat)} {regs : List Reg} (h : ModulusReady s B Z w N)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hf : Frm B rs s.mem t.mem)
    (hm : ∀ r ∈ rs, KMut r) (k : Keep regs s t) (h0 : .x0 ∉ regs)
    (ha : ∀ a ∈ modulusArrays, ∀ r ∈ rs,
      slot w a + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w a)
    (hi : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv)
    (he : ∀ r ∈ rs, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE) :
    ModulusReady t B Z w N := by
  have hz := h.ws.scr.nowrap
  have hw := h.ws.w1
  have fixed (a : Nat) (hm : a ∈ modulusArrays) :
      wv t.mem B (slot w a) w = wv s.mem B (slot w a) w := by
    have ha16 : a < 16 := by
      simp only [modulusArrays, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide
    have hb := h.ws.sl ha16
    exact hf.wv_eq (ha a hm) (by omega)
  refine ⟨h.ws.congr' hf hm k h0, ?_, (fixed aN (by simp [modulusArrays])).trans h.modulus,
    (fixed aOne (by simp [modulusArrays])).trans h.one,
    (fixed aR2 (by simp [modulusArrays])).trans h.r2,
    (fixed aR1 (by simp [modulusArrays])).trans h.r1,
    (fixed aRm1 (by simp [modulusArrays])).trans h.rm1,
    h.exponent.of_frm hf he (by omega)⟩
  rw [hf.word_eq (fun r hr => by have := ha aN (by simp [modulusArrays]) r hr; omega)
      (by have := h.ws.sl (show aN < 16 by decide); omega),
    hf.word_eq hi (by have := h.ws.h256; simp only [sMinv]; omega)]
  exact h.inverse

end VG.Proof.Dsa.AArch64.Generation
