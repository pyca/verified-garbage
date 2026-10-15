module

public import VerifiedGarbage.Impl.Dsa.X86.Minus
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Weierstrass.X86.Copy

/-! # Exact non-underflowing subtraction from the loaded modulus -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem modulusMinus_ok {s : State} {base : Addr} {size n m amount : Nat}
    (h : Context n m base size s) (ha : amount ≤ m) :
    WP isa (.block (modulusMinus n amount)) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 6) n = m - amount ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps [.eax] s t := by
  have hn0 : 0 < n := h.modulus.n0
  have hv : wordsVal s.mem base (slot n 0) n = m := h.modulus.val
  have hm : m < 2 ^ (64 * n) := by rw [← hv]; exact wordsVal_lt _ _ _ _
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by
    have := slot_bound (n := n) hj
    have := h.size_le
    simp only [stride] at *
    omega
  have sep60 := slot_sep (n := n) (i := 6) (j := 0) (by decide)
  have sep67 := slot_sep (n := n) (i := 6) (j := 7) (by decide)
  have sep70 := slot_sep (n := n) (i := 7) (j := 0) (by decide)
  simp only [stride] at sep60 sep67 sep70
  unfold modulusMinus
  refine WP.block_append (WP.mono (VG.Proof.Weierstrass.X86.setConst_ok h.scr (bounds 7 (by decide))
    (Nat.lt_of_le_of_lt ha hm)) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have Cu := h.outside_keep Ku (by decide) (by decide) Ou (by omega) (by have := slot_header n 7; omega)
  have Mu : wordsVal u.mem base (slot n 0) n = m := Cu.modulus.val
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega⟩
  rw [chain_eq]
  change WP isa (.block (chainK .sub .sbb (slot n 6) (slot n 0) (slot n 7) (2 * n))) u _
  rw [hk]
  refine WP.mono (chainSub_ok Cu.scr k (by have := bounds 6 (by decide); omega)
    (by have := bounds 0 (by decide); omega) (by have := bounds 7 (by decide); omega)
    (by omega) (by omega)) fun t ⟨Ot, ⟨c, _, Vt⟩, Kt⟩ => ?_
  have Ol : Outside base (slot n 6) (8 * n) u.mem t.mem := by
    simpa only [show 4 * (k + 1) = 8 * n by omega] using Ot
  have Ct := Cu.outside_keep Kt (by decide) (by decide) Ol (by omega) (by have := slot_header n 6; omega)
  refine ⟨Ct, ?_, (slotOutside_whole Ou (by decide)).trans (slotOutside_whole Ol (by decide)), Ku.trans Kt⟩
  rw [wordsVal_eq_val32, hk] at Mu Vu ⊢
  rw [Mu, Vu] at Vt
  have lt := val32_lt t.mem base (slot n 6) (k + 1)
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at Vt <;> omega

end VG.Proof.Dsa.X86
