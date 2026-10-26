module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core

/-! # Public workspace invariants between the reduction's arithmetic pieces -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG.Proof.Rsa
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.MlKem.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

structure ReductionPublic where
  B : Addr
  Z : Nat
  w : Nat
  x : Nat
  q : Nat

def ReductionStart (p : ReductionPublic) (s : State) : Prop :=
  Ws s p.B p.Z p.w ∧ wv s.mem p.B (slot p.w 0) p.w = p.x ∧
    wv s.mem p.B (slot p.w 2) p.w = 2 * p.q ∧ 0 < p.q

def ReductionCopied (p : ReductionPublic) (s : State) : Prop :=
  ReductionStart p s ∧ wv s.mem p.B (slot p.w 4) p.w = p.x

def ReductionDivided (p : ReductionPublic) (s : State) : Prop :=
  Ws s p.B p.Z p.w ∧ wv s.mem p.B (slot p.w 4) p.w = p.x ∧
    wv s.mem p.B (slot p.w 1) (p.w + 1) = p.x % (2 * p.q)

def ReductionSubtracted (p : ReductionPublic) (s : State) : Prop :=
  Ws s p.B p.Z p.w ∧ wv s.mem p.B (slot p.w 5) p.w % 2 = 0

theorem reductionCopy_state {p : ReductionPublic} {s : State} (h : ReductionStart p s) :
    WP isa (copyA 4 0) s (ReductionCopied p) := by
  refine WP.mono (copyA_ok h.1 (by decide : 4 < 16) (by decide : 0 < 16) (by decide))
    fun t ⟨hv, ho, hk⟩ => ?_
  have f : Frm p.B [ar p.w 4] s.mem t.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (p.w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  have ht := h.1.congr f (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) hk (by decide)
  have same (j : Nat) (hj : j < 4) : wv t.mem p.B (slot p.w j) p.w = wv s.mem p.B (slot p.w j) p.w := by
    apply f.wv_eq
    · simp only [List.mem_singleton]; rintro r rfl
      left
      simp only [slot, hdrBytes]
      have hm := Nat.mul_le_mul_right (8 * (p.w + 2)) (show j + 1 ≤ 4 by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
    · have := h.1.sl (show j < 16 by omega); have := h.1.scr.nowrap; omega
  exact ⟨⟨ht, (same 0 (by decide)).trans h.2.1, (same 2 (by decide)).trans h.2.2.1, h.2.2.2⟩,
    hv.trans h.2.1⟩

theorem reductionDivide_state {p : ReductionPublic} {s : State} (h : ReductionCopied p s) :
    WP isa (divmod 0 1 2 3) s (ReductionDivided p) := by
  have hw := h.1.1
  refine WP.mono (candidateDivision_ok hw.scr hw.rdi hw.hw hw.hS
    (by have := hw.w1; omega) hw.w2 hw.hZ (iQ := 0) (iR := 1) (iD := 2) (iT := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h.1.2.1 h.1.2.2.1 h.1.2.2.2)
    fun t ⟨_, f, hk, hr, _, _⟩ => ?_
  have ht := hw.congr f (fun r hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) hk (by decide)
  refine ⟨ht, ?_, hr⟩
  rw [f.wv_eq (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [slot, hdrBytes] <;> omega)
    (by have := hw.sl (by decide : 4 < 16); have := hw.scr.nowrap; omega)]
  exact h.2

theorem reductionSubtract_state {p : ReductionPublic} {s : State} (h : ReductionDivided p s) :
    WP isa (Impl.Dsa.X86_64.Generation.subtractRemainder 5 4 1) s (ReductionSubtracted p) := by
  have hbound : p.x < 2 ^ (64 * p.w) := h.2.1 ▸ wv_lt s.mem p.B (slot p.w 4) p.w
  have low : wv s.mem p.B (slot p.w 1) p.w = p.x % (2 * p.q) := by
    rw [wv_low_of_lt (Nat.le_succ p.w) (by rw [h.2.2]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hbound), h.2.2]
  refine WP.mono (subtractRemainder_ok h.1 (by decide : 5 < 16) (by decide : 4 < 16)
    (by decide : 1 < 16) (by decide) (by decide) (by rw [low, h.2.1]; exact Nat.mod_le _ _))
    fun t ⟨hv, ho, hk⟩ => ?_
  have f : Frm p.B [ar p.w 5] s.mem t.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (p.w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  refine ⟨h.1.congr f (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) hk (by decide), ?_⟩
  rw [hv, h.2.1, low]
  have hm := Nat.mod_add_div p.x (2 * p.q)
  have he : p.x - p.x % (2 * p.q) = 2 * p.q * (p.x / (2 * p.q)) := by omega
  rw [he]
  simp [Nat.mul_assoc]

end VG.Proof.Dsa.X86_64.Generation
