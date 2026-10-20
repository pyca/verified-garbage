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

/-- Return the public leading byte and exponent length without changing inputs. -/
theorem scan_inputs {p : GkP} {rb : List Byte} {s : State} (h : Inputs p rb s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.GenerateKey.bound) s fun t =>
      Inputs p rb t ∧ word t.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n ∧
      t.gpr .rax = p.bc.setWidth 64 ∧ Frm p.B scanRanges s.mem t.mem ∧
      Keep [.rsi, .rcx, .rax, .rbp, .rdx] s t := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have hZ := h.base.hZ
  refine WP.mono (bound_ok (B := p.B) (Z := p.Z) (k := p.k) (dl := p.dl) (dp := p.dp) (dom := p.dom)
    h.base.scr h.rdi (by omega) (by omega) (by omega) h.base.dl h.base.doml
    (h.base.hdr (sDom, p.dp) (by simp [GkP.headers])) h.q
    (h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers]))
    (h.base.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [GkP.headers])) h.base.dom)
    fun t ⟨hne, _, hn, hax, hf, k⟩ => ?_
  have hf' : Frm p.B scanRanges s.mem t.mem := hf.mono (by simp [scanRanges])
  refine ⟨h.keep hf' k (by decide), hn, ?_, hf', k⟩
  rw [hax]
  simp only [GkP.bc, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (lead_lt hne), Option.getD_some]

/-- Save the exact leading-byte mask, preserving the scanned length. -/
theorem smear_inputs {p : GkP} {rb : List Byte} {s : State} (h : Inputs p rb s)
    (hn : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n) (hax : s.gpr .rax = p.bc.setWidth 64) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.smear) s fun t =>
      Inputs p rb t ∧ word t.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n ∧
      word t.mem p.B (8 * sMsk) = p.msk ∧ Frm p.B scanRanges s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  have hZ := h.base.hZ
  refine WP.mono (smear_ok h.base.scr h.rdi (by omega) hax) fun t ⟨hm, hf, k⟩ => ?_
  have hf' : Frm p.B scanRanges s.mem t.mem := hf.mono (by simp [scanRanges])
  refine ⟨h.keep hf' k (by decide), ?_, hm, hf', k⟩
  rw [hf.word_eq (by simp; decide) (by decide)]
  exact hn

end VG.Proof.Ffdh.X86_64.GenerateKey
