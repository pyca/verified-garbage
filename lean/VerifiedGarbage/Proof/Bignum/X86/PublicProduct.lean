module

public import VerifiedGarbage.Impl.Bignum.X86.PublicExponent
public import VerifiedGarbage.Proof.Bignum.X86.PublicMath
public import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import all Init.Data.Nat.Bitwise.Basic

/-! # The masked multiply in right-to-left exponentiation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

def productRanges (n : Nat) : List (Nat × Nat) :=
  [(136, 4), (slot n 5, 8 * n), (slot n 7, 8 * n), (slot n 1, 8 * n), (slot n 2, 16 * n + 4)]

theorem exponentProduct_ok {n bytes m y b : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s)
    (hy : wordsVal s.mem base (slot n 7) n = y * 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 6) n = b * 2 ^ (64 * n) % m) :
    WP isa (exponentProduct n) s fun t =>
      Context n m base bytes t ∧
      wordsVal t.mem base (slot n 7) n =
        (if w32 s.mem base (128) % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      Outs base (productRanges n) s.mem t.mem ∧ Keeps clob s t := by
  have sz := h.size_le
  have bn := h.mod.n0
  change 0 < n at bn
  have nw := h.scr.nowrap
  have bh := slot_header n 8

  have hh0 := slot_header n 0

  have h5 := slot_header n 5
  have h6 := slot_header n 6
  have h7 := slot_header n 7
  have h1 := slot_header n 1
  have h2 := slot_header n 2
  have bh' : 256 ≤ bytes := by change slot n 8 ≤ bytes at sz; omega
  unfold exponentProduct
  refine WP.seq (WP.mono (exponentMask_ok h.scr (by change 128 + 4 ≤ bytes; omega) (by change 136 + 4 ≤ bytes; omega))
    fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have c₁ := h.outside_keep K₁ (by decide) (by decide) O₁ (.inr (by change 136 + 4 ≤ slot n 0; omega)) (by decide)
  have keep₁ (i : Nat) (hi : i < 8) :
      wordsVal s₁.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
    have hd := slot_header n i
    have bd := slot_bound (n := n) hi
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O₁.val32 (by change slot n i + 4 * (2 * n) ≤ 136 ∨ 136 + 4 ≤ slot n i; omega) (by unfold stride at bd; omega)
  have hb₁ : wordsVal s₁.mem base (slot n 6) n < m := by
    rw [keep₁ 6 (by decide), hb]
    exact Nat.mod_lt _ (by have := h.gt_one; omega)
  refine WP.seq (WP.mono (multiply_ok c₁ (o := 5) (a := 7) (b := 6)
    (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
    (by decide) (by decide) (by decide) (by decide) hb₁)
    fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  simp only [maskOffset, exponentOffset] at V₁
  have mask₂ : s₂.mem.readW (off base 136) 32 =
      if decide (w32 s.mem base (128) % 2 = 1) then BitVec.allOnes 32 else 0 := by
    rw [OpKeep.read32 K₂ (.inl (by change 136 + 4 ≤ slot n 5; omega)) (.inl (by change 140 ≤ slot n 1; omega))
      (.inl (by change 136 + 4 ≤ slot n 2; omega)) (by decide), V₁]
    simp only [decide_eq_true_eq]
    rfl
  have b6 := slot_bound (n := n) (i := 7) (by decide)
  have b7 := slot_bound (n := n) (i := 5) (by decide)
  have sep67 := slot_le (n := n) (i := 5) (j := 7) (by decide)
  refine WP.mono (selectProduct_ok (M := modulus n) c₂.scr
    (by change slot n 7 + 8 * n ≤ bytes; unfold stride at b6; omega)
    (by change slot n 5 + 8 * n ≤ bytes; unfold stride at b7; omega)
    (by change 136 + 4 ≤ bytes; omega) (.inr (.inr (by change slot n 5 + 8 * n ≤ slot n 7; unfold stride at sep67; omega)))
    _ mask₂ bn) fun t ⟨O₃, V₃, K₃⟩ => ?_
  have sep06 := slot_le (n := n) (i := 0) (j := 7) (by decide)
  refine ⟨c₂.outside_keep K₃ (by decide) (by decide) O₃
    (.inl (by unfold stride at sep06; omega)) (by change 56 + 4 ≤ slot n 7; omega), ?_, ?_, ?_⟩
  · have vp : wordsVal s₂.mem base (slot n 5) n = y * b * 2 ^ (64 * n) % m := by
      have v := VG.Proof.Dsa.mont_product h.coprime
        (a := y) (b := b) (by rw [keep₁ 7 (by decide), hy, Nat.mod_mod])
        (by rw [keep₁ 6 (by decide), hb, Nat.mod_mod]) V₂
      rwa [Nat.mod_eq_of_lt lt₂] at v
    have vy : wordsVal s₂.mem base (slot n 7) n = y * 2 ^ (64 * n) % m := by
      rw [slot_value c₁ (by unfold operand; decide) (by decide) (by decide) K₂,
        keep₁ 7 (by decide), hy]
    simp only [modulus, decide_eq_true_eq] at V₃
    rw [V₃]
    split <;> rename_i hk
    · simpa only [hk, ite_true] using vp
    · simpa only [hk, ite_false] using vy
  · have o₁ : Outs base (productRanges n) s.mem s₁.mem := Outs.of_outside O₁ (by simp [productRanges, maskOffset])
    have o₂ : Outs base (productRanges n) s₁.mem s₂.mem := K₂.mem.mono (by
      simp only [modulus, productRanges, List.mem_cons, List.not_mem_nil, or_false]
      intro r hr
      rcases hr with rfl | rfl | rfl <;> simp [accLen, words] <;> omega)
    exact (o₁.trans o₂).trans (Outs.of_outside O₃ (by simp [productRanges, modulus]))
  · exact ((K₁.mono (by decide)).trans (OpKeep.keeps K₂)).trans (K₃.mono (by decide))

theorem product_slot {n i : Nat} {base : Addr} {s t : State}
    (O : Outs base (productRanges n) s.mem t.mem) (hi : operand i)
    (hi1 : i ≠ 1) (hi5 : i ≠ 5) (hi7 : i ≠ 7) (hn : size n ≤ 2 ^ 64) :
    wordsVal t.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
  have h1 := slot_sep (n := n) hi1
  have h2 := acc_sep (n := n) hi
  have h5 := slot_sep (n := n) hi5
  have h7 := slot_sep (n := n) hi7
  have hd := slot_header n i
  have bd := slot_bound (n := n) hi.1
  simp only [stride, acc_length] at *
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega
  · omega

theorem product_exponent {n : Nat} {base : Addr} {s t : State}
    (O : Outs base (productRanges n) s.mem t.mem) :
    val32 t.mem base 128 2 = val32 s.mem base 128 2 := by
  have h1 := slot_header n 1
  have h2 := slot_header n 2
  have h5 := slot_header n 5
  have h7 := slot_header n 7
  apply O.val32
  · intro r hr
    simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega
  · decide

end VG.Proof.Bignum.X86.PublicContext
