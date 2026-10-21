module
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.DynamicOps

import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Runtime context invariants across modular operations -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

structure Context (n m : Nat) (base : Addr) (size : Nat) (s : State) : Prop where
  scr : Scr s base size
  size_le : contextBytes n ≤ size
  modulus : Modulus (contextMod n) size m s.mem base
  gt_one : 1 < m
  inverse : (m * w32 s.mem base 0 + 1) % 2 ^ 32 = 0

theorem context_slot_val {n size m o i : Nat} {base : Addr} {s t : State}
    (h : Context n m base size s) (hi : i < 9) (hio : i ≠ o) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t) :
    wordsVal t.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
  have so := slot_sep (n := n) hio
  have st := slot_sep (n := n) hi1
  have sa := slot_sep (n := n) hi2
  have bi := slot_bound (n := n) hi
  have sz := h.size_le
  have nw := h.scr.nowrap
  simp only [stride] at *
  apply OpKeep.val K
  · change slot n i + 8 * n ≤ slot n o ∨ slot n o + 8 * n ≤ slot n i
    omega
  · change slot n i + 8 * n ≤ slot n 1 ∨ slot n 1 + 8 * n ≤ slot n i
    omega
  · rw [context_accLen]; omega
  · omega

theorem Context.keep {n size m o : Nat} {base : Addr} {s t : State}
    (h : Context n m base size s) (ho0 : o ≠ 0)
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t) : Context n m base size t := by
  refine ⟨h.scr.of_keeps (OpKeep.keeps K) (by decide), h.size_le, ?_, h.gt_one, ?_⟩
  · refine ⟨h.modulus.n0, h.modulus.mo, h.modulus.tmp, h.modulus.sep, ?_⟩
    change wordsVal t.mem base (slot n 0) n = m
    rw [context_slot_val h (by decide) (Ne.symm ho0) (by decide) (by decide) K]
    exact h.modulus.val
  · have he : w32 t.mem base 0 = w32 s.mem base 0 := by
      have hv : val32 t.mem base 0 1 = val32 s.mem base 0 1 := by
        apply K.mem.val32
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          have h0 := slot_header n o
          have h1 := slot_header n 1
          have h2 := slot_header n 2
          rcases hr with rfl | rfl | rfl <;> simp only [contextMod] <;> omega
        · decide
      simpa only [val32, Nat.mul_zero, Nat.add_zero] using hv
    rw [he]; exact h.inverse

/-- Preserve the arithmetic context across writes to any collection of
ranges disjoint from its modulus and inverse. -/
theorem Context.outs_keep {n size m : Nat} {base : Addr} {s t : State}
    (h : Context n m base size s) {regs : List Reg} {ranges : List (Nat × Nat)}
    (K : Keeps regs s t) (hdi : .edi ∉ regs) (hsp : .esp ∉ regs)
    (O : Outs base ranges s.mem t.mem)
    (hm : ∀ r ∈ ranges, slot n 0 + 8*n ≤ r.1 ∨ r.1+r.2 ≤ slot n 0)
    (hi : ∀ r ∈ ranges, 4 ≤ r.1) : Context n m base size t := by
  refine ⟨h.scr.of_keeps K hdi hsp, h.size_le, ?_, h.gt_one, ?_⟩
  · refine ⟨h.modulus.n0, h.modulus.mo, h.modulus.tmp, h.modulus.sep, ?_⟩
    change wordsVal t.mem base (slot n 0) n = m
    rw [wordsVal_eq_val32, O.val32 (fun r hr => by have := hm r hr; omega)
      (by have := h.scr.nowrap; have := h.modulus.mo; change slot n 0 + 8*n ≤ size at this; omega),
      ← wordsVal_eq_val32]
    exact h.modulus.val
  · have same := O.val32 (d := 0) (k := 1) (fun r hr => Or.inl (by have := hi r hr; omega)) (by decide)
    have word : w32 t.mem base 0 = w32 s.mem base 0 := by
      simpa only [val32, Nat.mul_zero, Nat.add_zero] using same
    rw [word]; exact h.inverse

theorem Context.outside_keep {n size m d len : Nat} {base : Addr} {s t : State}
    (h : Context n m base size s) {rs : List Reg} (K : Keeps rs s t) (hdi : .edi ∉ rs) (hsp : .esp ∉ rs)
    (O : Outside base d len s.mem t.mem)
    (hm : slot n 0 + 8 * n ≤ d ∨ d + len ≤ slot n 0)
    (hi : 4 ≤ d) : Context n m base size t := by
  exact h.outs_keep K hdi hsp (ranges := [(d, len)]) (Outs.of_outside O (by simp))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hm)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hi)

theorem context_slot_val32 {n size m o i k : Nat} {base : Addr} {s t : State}
    (h : Context n m base size s) (hi : i < 9) (hk : k ≤ 2 * n)
    (hio : i ≠ o) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t) :
    val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k := by
  have so := slot_sep (n := n) hio
  have st := slot_sep (n := n) hi1
  have sa := slot_sep (n := n) hi2
  have bi := slot_bound (n := n) hi
  have sz := h.size_le
  have nw := h.scr.nowrap
  simp only [stride] at *
  apply K.mem.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [contextMod, accLen, words] <;> omega
  · omega

end VG.Proof.Mont.X86.Dynamic
