module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Round
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Preparing the round's minus-one comparison without disturbing its residue -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem roundMinusOne_ok {s : State} {base : Addr} {size n m : Nat}
    (h : Context n m base size s) (one : wordsVal s.mem base (slot n 3) n = 1) :
    WP isa (roundMinusOne n) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 8) n = m - 1 ∧
      Outside base (slot n 8) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hn0 : 0 < n := h.modulus.n0
  have gt := h.gt_one
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by
    have := slot_bound (n := n) hj
    have := h.size_le
    simp only [stride] at *
    omega
  have sep80 := slot_sep (n := n) (i := 8) (j := 0) (by decide)
  have sep83 := slot_sep (n := n) (i := 8) (j := 3) (by decide)
  simp only [stride] at sep80 sep83
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega⟩
  unfold roundMinusOne
  rw [hk]
  refine WP.mono (chainSubW_ok h.scr (k := k + 1) (by omega) (by have := bounds 8 (by decide); omega)
    (by have := bounds 0 (by decide); omega) (by have := bounds 3 (by decide); omega)
    (by omega) (by omega)) fun t ⟨Ot, ⟨c, _, Vt⟩, Kt⟩ => ?_
  have Ol : Outside base (slot n 8) (8 * n) s.mem t.mem := by
    simpa only [show 4 * (k + 1) = 8 * n by omega] using Ot
  refine ⟨h.outside_keep Kt (by decide) (by decide) Ol (by omega) (by have := slot_header n 8; omega), ?_, Ol, Kt.mono (by decide)⟩
  have modulus : wordsVal s.mem base (slot n 0) n = m := h.modulus.val
  rw [wordsVal_eq_val32, hk] at modulus one ⊢
  rw [modulus, one] at Vt
  have lt := val32_lt t.mem base (slot n 8) (k + 1)
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at Vt <;> omega
end VG.Proof.Dsa.X86.Generation
