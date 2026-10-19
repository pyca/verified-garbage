module

public import VerifiedGarbage.Proof.Mont.X86.WindowTable
public import VerifiedGarbage.Proof.Mont.X86.WindowWords
public import VerifiedGarbage.Proof.Mont.X86.ExponentBody

/-! # One window: four squares and a multiplication by the window's entry -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

theorem square_ok {n size m y : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hy : wordsVal s.mem base (slot n 6) n = y * 2 ^ (64 * n) % m) :
    WP isa (square n) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n 6) s t ∧
      wordsVal t.mem base (slot n 6) n = y ^ 2 * 2 ^ (64 * n) % m := by
  refine WP.mono (context_mul_ok h (o := 6) (a := 6) (b := 6)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hy]; exact Nat.mod_lt _ (by have := h.gt_one; omega))) fun t ⟨c, K, lt, V⟩ => ⟨c, K, ?_⟩
  have v := VG.Proof.Dsa.mont_product h.coprime (a := y) (b := y)
    (by rw [hy, Nat.mod_mod]) (by rw [hy, Nat.mod_mod]) V
  rwa [Nat.mod_eq_of_lt lt, ← Nat.pow_two] at v

/-- Four squares. -/
theorem squares_ok {n size m tab y k : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size) (hk : k ≤ 2 * n)
    (hy : wordsVal s.mem base (slot n 6) n = y * 2 ^ (64 * n) % m) :
    WP isa (squares n) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n = y ^ 16 * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) k = val32 s.mem base (slot n 8) k ∧
      (∀ j < 16, wordsVal t.mem base (entry n tab j) n = wordsVal s.mem base (entry n tab j) n) ∧
      Outs base (exponentRanges n k) s.mem t.mem ∧ Keeps clob s t := by
  unfold squares
  refine WP.seq (WP.mono (square_ok h hy) fun s₁ ⟨c₁, K₁, Y₁⟩ => ?_)
  refine WP.seq (WP.mono (square_ok c₁ Y₁) fun s₂ ⟨c₂, K₂, Y₂⟩ => ?_)
  refine WP.seq (WP.mono (square_ok c₂ Y₂) fun s₃ ⟨c₃, K₃, Y₃⟩ => ?_)
  refine WP.mono (square_ok c₃ Y₃) fun t ⟨ct, Kt, Yt⟩ => ⟨ct, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Yt, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
  · rw [context_slot_val32 c₃ (by decide) hk (by decide) (by decide) (by decide) Kt,
      context_slot_val32 c₂ (by decide) hk (by decide) (by decide) (by decide) K₃,
      context_slot_val32 c₁ (by decide) hk (by decide) (by decide) (by decide) K₂,
      context_slot_val32 h (by decide) hk (by decide) (by decide) (by decide) K₁]
  · intro j hj
    rw [op_table_keep c₃ W Kt (by decide) hj, op_table_keep c₂ W K₃ (by decide) hj,
      op_table_keep c₁ W K₂ (by decide) hj, op_table_keep h W K₁ (by decide) hj]
  · exact (((exponentRanges_op K₁ (.inr rfl)).trans (exponentRanges_op K₂ (.inr rfl))).trans
      (exponentRanges_op K₃ (.inr rfl))).trans (exponentRanges_op Kt (.inr rfl))
  · exact (((OpKeep.keeps K₁).trans (OpKeep.keeps K₂)).trans (OpKeep.keeps K₃)).trans (OpKeep.keeps Kt)

/-- The window word from the exponent's top four bits, and the exponent shifted up. -/
theorem nextWindow_ok {n size m tab k : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size) (hk0 : 0 < k) (hk : k ≤ 2 * n) :
    WP isa (.block (topWindow (slot n 8) k ++ shiftUp k (slot n 8))) s fun t =>
      Context n m base size t ∧
      w32 t.mem base 4 = val32 s.mem base (slot n 8) k * 16 / 2 ^ (32 * k) ∧
      val32 t.mem base (slot n 8) k = val32 s.mem base (slot n 8) k * 16 % 2 ^ (32 * k) ∧
      wordsVal t.mem base (slot n 6) n = wordsVal s.mem base (slot n 6) n ∧
      (∀ j < 16, wordsVal t.mem base (entry n tab j) n = wordsVal s.mem base (entry n tab j) n) ∧
      Outs base (exponentRanges n k) s.mem t.mem ∧ Keeps clob s t := by
  have sz := h.size_le
  have nw := h.scr.nowrap
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  have h8 := slot_header n 8
  have h08 := slot_le (n := n) (i := 0) (j := 8) (by decide)
  have h68 := slot_le (n := n) (i := 6) (j := 8) (by decide)
  have h00 := slot_header n 0
  have h6 := slot_header n 6
  have hc : 64 ≤ contextBytes n := slot_header n 9
  have ctx := W.ctx
  have fit := W.fit
  unfold stride at b8 h08 h68
  have expBound : slot n 8 + 4 * k ≤ size := by omega
  refine WP.block_append (WP.mono (topWindow_ok h.scr hk0 expBound (by omega)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have c₁ := h.outside_keep K₁ (by decide) (by decide) O₁ (.inr (by omega)) (by omega)
  refine WP.mono (shiftUp_ok c₁.scr k (slot n 8) expBound) fun t ⟨O₂, V₂, K₂⟩ => ?_
  have E₁ : val32 s₁.mem base (slot n 8) k = val32 s.mem base (slot n 8) k := O₁.val32 (by omega) (by omega)
  refine ⟨c₁.outside_keep K₂ (by decide) (by decide) O₂ (.inl (by omega)) (by omega), ?_, ?_, ?_, ?_, ?_,
    ((K₁.mono (by decide) : Keeps [.eax, .edx] s s₁).trans K₂).mono (by decide)⟩
  · rw [O₂.w32 (by omega) (by omega), V₁]
  · rw [V₂, E₁]
  · rw [O₂.wordsVal (.inl (by omega)) (by omega), O₁.wordsVal (.inr (by omega)) (by omega)]
  · intro j hj
    have := table_keep (n := n) (tab := tab) (j := j) (Outs.of_outside O₁ (rs := [(4, 4)]) (by simp))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega) (by omega) hj
    rw [← this]
    exact table_keep (Outs.of_outside O₂ (rs := [(slot n 8, 4 * k)]) (by simp))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega) (by omega) hj
  · exact (Outs.of_outside O₁ (by simp [exponentRanges, productRanges])).trans
      (Outs.of_outside O₂ (by simp [exponentRanges, productRanges]))

theorem windowBody_ok {n size m tab k b y : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size) (hk0 : 0 < k) (hk : k ≤ 2 * n)
    (ht : ∀ j < 16, wordsVal s.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m)
    (hy : wordsVal s.mem base (slot n 6) n = y * 2 ^ (64 * n) % m) :
    WP isa (windowBody n k tab) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n =
        y ^ 16 * b ^ (val32 s.mem base (slot n 8) k * 16 / 2 ^ (32 * k)) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) k = val32 s.mem base (slot n 8) k * 16 % 2 ^ (32 * k) ∧
      (∀ j < 16, wordsVal t.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m) ∧
      Outs base (exponentRanges n k) s.mem t.mem ∧ Keeps clob s t := by
  have hm0 : 0 < m := by have := h.gt_one; omega
  have nw := h.scr.nowrap
  have sz := h.size_le
  unfold windowBody
  refine WP.seq (WP.mono (squares_ok h W hk hy) fun s₁ ⟨c₁, Y₁, E₁, T₁, O₁, K₁⟩ => ?_)
  refine WP.seq (WP.mono (nextWindow_ok c₁ W hk0 hk) fun s₂ ⟨c₂, w₂, E₂, Y₂, T₂, O₂, K₂⟩ => ?_)
  have hw : w32 s₂.mem base 4 < 16 := by
    rw [w₂, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have := val32_lt s₁.mem base (slot n 8) k
    omega
  have L := W.tableLay c₂ (i := 7) (by decide)
  refine WP.seq (WP.mono (selectWindow_ok c₂.scr L hw) fun s₃ ⟨O₃, S₃, K₃⟩ => ?_)
  have h07 := slot_le (n := n) (i := 0) (j := 7) (by decide)
  have h67 := slot_le (n := n) (i := 6) (j := 7) (by decide)
  have h78 := slot_le (n := n) (i := 7) (j := 8) (by decide)
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  have h7 := slot_header n 7
  unfold stride at h07 h67 h78 b8
  have c₃ := c₂.outside_keep K₃ (by decide) (by decide) O₃ (.inl (by omega)) (by omega)
  have entry₂ : ∀ j < 16, wordsVal s₂.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m := by
    intro j hj; rw [T₂ j hj, T₁ j hj, ht j hj]
  have S₃' : wordsVal s₃.mem base (slot n 7) n = b ^ (w32 s₂.mem base 4) * 2 ^ (64 * n) % m := by
    rw [S₃, entry₂ _ hw]
  have ctx := W.ctx
  have fit := W.fit
  refine WP.mono (context_mul_ok c₃ (o := 6) (a := 6) (b := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [S₃']; exact Nat.mod_lt _ hm0)) fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ?_, ?_, ?_, ?_, ?_⟩
  · have Y₃ : wordsVal s₃.mem base (slot n 6) n = y ^ 16 * 2 ^ (64 * n) % m := by
      rw [O₃.wordsVal (.inl (by omega)) (by omega), Y₂, Y₁]
    have v := VG.Proof.Dsa.mont_product c₃.coprime (a := y ^ 16) (b := b ^ w32 s₂.mem base 4)
      (by rw [Y₃, Nat.mod_mod]) (by rw [S₃', Nat.mod_mod]) Vt
    rw [Nat.mod_eq_of_lt ltt, w₂, E₁] at v
    exact v
  · rw [context_slot_val32 c₃ (by decide) hk (by decide) (by decide) (by decide) Kt,
      O₃.val32 (.inr (by omega)) (by omega), E₂, E₁]
  · intro j hj
    have L' := L.entry (j := j) hj
    rw [op_table_keep c₃ W Kt (by decide) hj, O₃.wordsVal L'.2.1.symm (by omega), entry₂ j hj]
  · exact ((O₁.trans O₂).trans (Outs.of_outside O₃ (by simp [exponentRanges, productRanges]))).trans
      (exponentRanges_op Kt (.inr rfl))
  · exact ((K₁.trans K₂).trans (K₃.mono (by decide))).trans (OpKeep.keeps Kt)

end VG.Proof.Mont.X86.Dynamic
