module

public import VerifiedGarbage.Proof.Mont.X86.ExponentProduct
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.ShiftDown

/-! # The arithmetic and exponent update of one iteration -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

def exponentRanges (n expWords : Nat) : List (Nat × Nat) :=
  productRanges n ++ [(slot n 5, 8 * n), (slot n 8, 4 * expWords)]

theorem exponentBody_ok {n size m y b expWords : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 1 < expWords) (hen : expWords ≤ 2 * n)
    (hy : wordsVal s.mem base (slot n 6) n = y * 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 5) n = b * 2 ^ (64 * n) % m) :
    WP isa (exponentBody n expWords) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n =
        (if val32 s.mem base (slot n 8) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 5) n = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) expWords = val32 s.mem base (slot n 8) expWords / 2 ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Keeps clob s t := by
  have sz := h.size_le
  have nw := h.scr.nowrap
  have cn : contextBytes n ≤ 2 ^ 64 := by omega
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  have expBound : slot n 8 + 4 * expWords ≤ size := by unfold stride at b8; omega
  unfold exponentBody
  refine WP.seq (WP.mono (exponentProduct_ok h hy hb) fun s₁ ⟨c₁, Y₁, O₁, K₁⟩ => ?_)
  have B₁ : wordsVal s₁.mem base (slot n 5) n = b * 2 ^ (64 * n) % m := by
    rw [wordsVal_eq_val32, productRanges_val32 O₁ (by decide) (Nat.le_refl _) (by decide)
      (by decide) (by decide) (by decide) cn, ← wordsVal_eq_val32, hb]
  have E₁ := productRanges_val32 O₁ (i := 8) (by decide) hen (by decide) (by decide) (by decide) (by decide) cn
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 5) (a := 5) (b := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [B₁]; exact Nat.mod_lt _ (by have := h.gt_one; omega))) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have B₂ : wordsVal s₂.mem base (slot n 5) n = (b * b) * 2 ^ (64 * n) % m := by
    have v := VG.Proof.Dsa.mont_product h.coprime (a := b) (b := b)
      (by rw [B₁, Nat.mod_mod]) (by rw [B₁, Nat.mod_mod]) V₂
    rwa [Nat.mod_eq_of_lt lt₂] at v
  have Y₂ : wordsVal s₂.mem base (slot n 6) n = wordsVal s₁.mem base (slot n 6) n :=
    context_slot_val c₁ (by decide) (by decide) (by decide) (by decide) K₂
  have E₂ : val32 s₂.mem base (slot n 8) expWords = val32 s₁.mem base (slot n 8) expWords := by
    have h58 := slot_le (n := n) (i := 5) (j := 8) (by decide)
    have h18 := slot_le (n := n) (i := 1) (j := 8) (by decide)
    have h28 := slot_le (n := n) (i := 2) (j := 8) (by decide)
    apply K₂.mem.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [contextMod, accLen, words] <;>
        unfold stride at h58 h18 h28 <;> omega
    · omega
  refine WP.mono (shiftDown_ok c₂.scr he expBound) fun t ⟨O₃, E₃, K₃⟩ => ?_
  have h08 := slot_le (n := n) (i := 0) (j := 8) (by decide)
  have h8 := slot_header n 8
  refine ⟨c₂.outside_keep K₃ (by decide) (by decide) O₃
    (.inl (by unfold stride at h08; omega)) (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · have h68 := slot_le (n := n) (i := 6) (j := 8) (by decide)
    have b6 := slot_bound (n := n) (i := 6) (by decide)
    rw [wordsVal_eq_val32, O₃.val32 (by unfold stride at h68; omega)
      (by unfold stride at b6; omega), ← wordsVal_eq_val32, Y₂, Y₁]
    obtain ⟨k, rfl⟩ : ∃ k, expWords = k + 1 := ⟨expWords - 1, by omega⟩
    rw [val32_parity]
  · have h58 := slot_le (n := n) (i := 5) (j := 8) (by decide)
    have b5 := slot_bound (n := n) (i := 5) (by decide)
    rw [wordsVal_eq_val32, O₃.val32 (by unfold stride at h58; omega)
      (by unfold stride at b5; omega), ← wordsVal_eq_val32, B₂]
  · rw [E₃, E₂, E₁]
  · have o₁ : Outs base (exponentRanges n expWords) s.mem s₁.mem := O₁.mono (by
      intro r hr; exact List.mem_append_left _ hr)
    have o₂ : Outs base (exponentRanges n expWords) s₁.mem s₂.mem := K₂.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp [exponentRanges, productRanges, contextMod, accLen, words] <;> omega)
    exact (o₁.trans o₂).trans (Outs.of_outside O₃ (by simp [exponentRanges]))
  · exact (K₁.trans (OpKeep.keeps K₂)).trans (K₃.mono (by decide))

theorem exponentRanges_one {n expWords : Nat} {base : Addr} {s t : State}
    (O : Outs base (exponentRanges n expWords) s.mem t.mem)
    (hn : contextBytes n ≤ 2 ^ 64) :
    wordsVal t.mem base (slot n 3) n = wordsVal s.mem base (slot n 3) n := by
  have h13 := slot_le (n := n) (i := 1) (j := 3) (by decide)
  have h23 := slot_le (n := n) (i := 2) (j := 3) (by decide)
  have h35 := slot_le (n := n) (i := 3) (j := 5) (by decide)
  have h36 := slot_le (n := n) (i := 3) (j := 6) (by decide)
  have h37 := slot_le (n := n) (i := 3) (j := 7) (by decide)
  have h38 := slot_le (n := n) (i := 3) (j := 8) (by decide)
  have hd := slot_header n 3
  have bd := slot_bound (n := n) (i := 3) (by decide)
  simp only [stride] at *
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [exponentRanges, productRanges, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · omega

theorem exponentRanges_op {n expWords o : Nat} {base : Addr} {s t : State}
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t) (ho : o = 5 ∨ o = 6) :
    Outs base (exponentRanges n expWords) s.mem t.mem := by
  refine K.mem.mono ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases ho with rfl | rfl <;> simp [exponentRanges, productRanges, contextMod]
  · simp [exponentRanges, productRanges, contextMod]
  · simp [exponentRanges, productRanges, contextMod, accLen, words]
    omega

end VG.Proof.Mont.X86.Dynamic
