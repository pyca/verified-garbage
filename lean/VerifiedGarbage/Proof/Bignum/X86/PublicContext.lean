module

public import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # Preservation of the compact public RSA Montgomery context -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure Context (n m : Nat) (base : Addr) (bytes : Nat) (s : State) : Prop where
  scr : Scr s base bytes
  size_le : size n ≤ bytes
  mod : Modulus (modulus n) bytes m s.mem base
  gt_one : 1 < m
  inverse : (m * w32 s.mem base inverseOffset + 1) % 2 ^ 32 = 0

theorem slot_value {n bytes m o i : Nat} {base : Addr} {s t : State}
    (h : Context n m base bytes s) (hi : operand i) (hio : i ≠ o) (hi1 : i ≠ 1)
    (K : OpKeep (modulus n) base (slot n 2) (slot n o) s t) :
    wordsVal t.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
  have so := slot_sep (n := n) hio
  have st := slot_sep (n := n) hi1
  have sa := acc_sep (n := n) hi
  have bi := slot_bound (n := n) hi.1
  have sz := h.size_le
  have nw := h.scr.nowrap
  simp only [stride] at *
  apply OpKeep.val K
  · change slot n i + 8 * n ≤ slot n o ∨ slot n o + 8 * n ≤ slot n i
    omega
  · change slot n i + 8 * n ≤ slot n 1 ∨ slot n 1 + 8 * n ≤ slot n i
    omega
  · exact sa
  · omega

theorem header_word {n o d : Nat} {base : Addr} {s t : State}
    (hd : d + 4 ≤ 256)
    (K : OpKeep (modulus n) base (slot n 2) (slot n o) s t) :
    w32 t.mem base d = w32 s.mem base d := by
  have hv : val32 t.mem base d 1 = val32 s.mem base d 1 := by
    apply K.mem.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have ho := slot_header n o
      have ht := slot_header n 1
      have ha := slot_header n 2
      rcases hr with rfl | rfl | rfl <;> simp only [modulus] <;> omega
    · omega
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using hv

theorem header_value {n o d k : Nat} {base : Addr} {s t : State}
    (hd : d + 4 * k ≤ 256)
    (K : OpKeep (modulus n) base (slot n 2) (slot n o) s t) :
    val32 t.mem base d k = val32 s.mem base d k := by
  apply K.mem.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have ho := slot_header n o
    have ht := slot_header n 1
    have ha := slot_header n 2
    rcases hr with rfl | rfl | rfl <;> simp only [modulus] <;> omega
  · omega

theorem Context.keep {n bytes m o : Nat} {base : Addr} {s t : State}
    (h : Context n m base bytes s) (ho0 : o ≠ 0)
    (K : OpKeep (modulus n) base (slot n 2) (slot n o) s t) : Context n m base bytes t := by
  refine ⟨h.scr.of_keeps (OpKeep.keeps K) (by decide), h.size_le, ?_, h.gt_one, ?_⟩
  · refine ⟨h.mod.n0, h.mod.mo, h.mod.tmp, h.mod.sep, ?_⟩
    change wordsVal t.mem base (slot n 0) n = m
    rw [slot_value h (by unfold operand; decide) (Ne.symm ho0) (by decide) K]
    exact h.mod.val
  · rw [header_word (by decide) K]
    exact h.inverse

theorem multiply_ok {n bytes m o a b : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s) (ho : operand o) (ha : operand a) (hb : operand b)
    (ho0 : o ≠ 0) (ho1 : o ≠ 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hB : wordsVal s.mem base (slot n b) n < m) :
    WP isa (multiply n o a b) s fun t =>
      Context n m base bytes t ∧
      OpKeep (modulus n) base (slot n 2) (slot n o) s t ∧
      wordsVal t.mem base (slot n o) n < m ∧
      wordsVal t.mem base (slot n o) n * 2 ^ (64 * n) % m =
        wordsVal s.mem base (slot n a) n * wordsVal s.mem base (slot n b) n % m := by
  have hdr := slot_header n 8
  have hdr2 := slot_header n 2
  have sz := h.size_le
  refine WP.mono (mul_ok h.scr h.mod
    (by change 56 + 4 ≤ bytes; change slot n 8 ≤ bytes at sz; omega)
    (.inl (by change 56 + 4 ≤ slot n 2; omega)) h.inverse
    (operation_layout h.size_le ho ha hb ho1) hB
    (by have := slot_sep (n := n) ha1; simp only [modulus, stride] at *; omega)
    (by have := slot_sep (n := n) hb1; simp only [modulus, stride] at *; omega)
    (by have := slot_header n 1; change 56 + 4 ≤ slot n 1 ∨ slot n 1 + 4 ≤ 56; omega))
    fun t ⟨K, lt, V⟩ => ⟨h.keep ho0 K, K, lt, V⟩

theorem Context.outside_keep {n bytes m d len : Nat} {base : Addr} {s t : State}
    (h : Context n m base bytes s) {rs : List Reg} (K : Keeps rs s t)
    (hdi : .edi ∉ rs) (hsp : .esp ∉ rs) (O : Outside base d len s.mem t.mem)
    (hm : slot n 0 + 8 * n ≤ d ∨ d + len ≤ slot n 0)
    (hi : inverseOffset + 4 ≤ d) : Context n m base bytes t := by
  refine ⟨h.scr.of_keeps K hdi hsp, h.size_le, ?_, h.gt_one, ?_⟩
  · refine ⟨h.mod.n0, h.mod.mo, h.mod.tmp, h.mod.sep, ?_⟩
    change wordsVal t.mem base (slot n 0) n = m
    rw [wordsVal_eq_val32, O.val32 (by omega)
      (by have := h.scr.nowrap; have := h.mod.mo; change slot n 0 + 8 * n ≤ bytes at this; omega),
      ← wordsVal_eq_val32]
    exact h.mod.val
  · rw [O.w32 (.inl hi) (by decide)]
    exact h.inverse

end VG.Proof.Bignum.X86.PublicContext
