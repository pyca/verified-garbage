module

public import VerifiedGarbage.Proof.Bignum.X86.PublicProduct
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift

/-! # One fixed-schedule RSA exponentiation iteration -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

def exponentRanges (n : Nat) : List (Nat × Nat) :=
  productRanges n ++ [(slot n 6, 8 * n), (128, 8)]

theorem exponentBody_ok {n bytes m y b : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s)
    (hy : wordsVal s.mem base (slot n 7) n = y * 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 6) n = b * 2 ^ (64 * n) % m) :
    WP isa (exponentBody n) s fun t =>
      Context n m base bytes t ∧
      wordsVal t.mem base (slot n 7) n =
        (if val32 s.mem base 128 2 % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 6) n = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base 128 2 = val32 s.mem base 128 2 / 2 ∧
      Outs base (exponentRanges n) s.mem t.mem ∧ Keeps clob s t := by
  have sz := h.size_le
  have nw := h.scr.nowrap
  have cn : size n ≤ 2 ^ 64 := by omega
  have header := slot_header n 8
  have expBound : 128 + 4 * 2 ≤ bytes := by change slot n 8 ≤ bytes at sz; omega
  unfold exponentBody
  refine WP.seq (WP.mono (exponentProduct_ok h hy hb) fun s₁ ⟨c₁, Y₁, O₁, K₁⟩ => ?_)
  have B₁ : wordsVal s₁.mem base (slot n 6) n = b * 2 ^ (64 * n) % m := by
    rw [product_slot O₁ (by unfold operand; decide) (by decide) (by decide) (by decide) cn, hb]
  have E₁ := product_exponent O₁
  refine WP.seq (WP.mono (multiply_ok c₁ (o := 6) (a := 6) (b := 6)
    (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [B₁]; exact Nat.mod_lt _ (by have := h.gt_one; omega))) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have B₂ : wordsVal s₂.mem base (slot n 6) n = (b * b) * 2 ^ (64 * n) % m := by
    have v := VG.Proof.Dsa.mont_product h.coprime (a := b) (b := b)
      (by rw [B₁, Nat.mod_mod]) (by rw [B₁, Nat.mod_mod]) V₂
    rwa [Nat.mod_eq_of_lt lt₂] at v
  have Y₂ : wordsVal s₂.mem base (slot n 7) n = wordsVal s₁.mem base (slot n 7) n :=
    slot_value c₁ (by unfold operand; decide) (by decide) (by decide) K₂
  have E₂ : val32 s₂.mem base 128 2 = val32 s₁.mem base 128 2 := header_value (by decide) K₂
  refine WP.mono (shiftExponent_ok c₂.scr 2 128 expBound) fun t ⟨O₃, E₃, K₃⟩ => ?_
  have h0 := slot_header n 0
  have h6 := slot_header n 6
  have h7 := slot_header n 7
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  refine ⟨c₂.outside_keep K₃ (by decide) (by decide) O₃
    (.inr (by omega)) (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [wordsVal_eq_val32, O₃.val32 (by omega) (by unfold stride at b7; omega),
      ← wordsVal_eq_val32, Y₂, Y₁, val32_parity]
  · rw [wordsVal_eq_val32, O₃.val32 (by omega) (by unfold stride at b6; omega),
      ← wordsVal_eq_val32, B₂]
  · rw [E₃, E₂, E₁]
  · have o₁ : Outs base (exponentRanges n) s.mem s₁.mem := O₁.mono (by
      intro r hr; exact List.mem_append_left _ hr)
    have o₂ : Outs base (exponentRanges n) s₁.mem s₂.mem := K₂.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp [exponentRanges, productRanges, modulus, accLen, words] <;> omega)
    exact (o₁.trans o₂).trans (Outs.of_outside O₃ (by simp [exponentRanges]))
  · exact (K₁.trans (OpKeep.keeps K₂)).trans (K₃.mono (by decide))

theorem exponent_one {n : Nat} {base : Addr} {s t : State}
    (O : Outs base (exponentRanges n) s.mem t.mem) (hn : size n ≤ 2 ^ 64) :
    wordsVal t.mem base (slot n 4) n = wordsVal s.mem base (slot n 4) n := by
  have h1 := slot_le (n := n) (i := 1) (j := 4) (by decide)
  have h2 := acc_end n
  have h5 := slot_le (n := n) (i := 4) (j := 5) (by decide)
  have h6 := slot_le (n := n) (i := 4) (j := 6) (by decide)
  have h7 := slot_le (n := n) (i := 4) (j := 7) (by decide)
  have hd := slot_header n 4
  have bd := slot_bound (n := n) (i := 4) (by decide)
  simp only [stride, acc_length] at *
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [exponentRanges, productRanges, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · omega

theorem exponent_op {n o : Nat} {base : Addr} {s t : State}
    (K : OpKeep (modulus n) base (slot n 2) (slot n o) s t) (ho : o = 6 ∨ o = 7) :
    Outs base (exponentRanges n) s.mem t.mem := by
  refine K.mem.mono ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases ho with rfl | rfl <;> simp [exponentRanges, productRanges, modulus]
  · simp [exponentRanges, productRanges, modulus]
  · simp [exponentRanges, productRanges, modulus, accLen, words]
    omega

end VG.Proof.Bignum.X86.PublicContext
