module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH on x86-64: the bound scan preserves the key-generation inputs -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Domain and random input with initialized y, before scalar sampling. -/
structure Inputs (p : GkP) (rb : List Byte) (s : State) : Prop where
  base : Base p rb s
  rdi : s.gpr .rdi = p.B
  y : Src s p.B p.Z p.yp (List.replicate p.k 0)
  g : word s.mem p.B (8 * sG) = off p.dp p.k
  q : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)

/-- Header changes made while scanning or masking the bound. -/
def scanRanges : List (Nat × Nat) := [(8 * sEp, 8), (8 * sEl, 8), (8 * sMsk, 8)]

theorem scanRanges_end : ∀ r ∈ scanRanges, r.1 + r.2 ≤ 256 := by
  simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> decide

theorem Inputs.keep {p : GkP} {rb : List Byte} {s t : State} {rs : List Reg} (h : Inputs p rb s)
    (hf : Frm p.B scanRanges s.mem t.mem) (k : Keep rs s t) (hdi : .rdi ∉ rs) : Inputs p rb t := by
  have hZ := h.base.hZ
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [sEp, sEl, sMsk, sFn] <;> omega)
  have hh : ∀ i < 32, i ≠ sEp → i ≠ sEl → i ≠ sMsk →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi he hl hm =>
    hf.word_eq (by
      simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> simp only <;> omega) (by omega)
  refine ⟨h.base.keep hi k ?_, (k.gpr hdi).trans h.rdi, h.y.congrK hi k,
    (hh _ (by decide) (by decide) (by decide) (by decide)).trans h.g,
    (hh _ (by decide) (by decide) (by decide) (by decide)).trans h.q⟩
  intro e he
  simp only [GkP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)

end VG.Proof.Ffdh.X86_64.GenerateKey
