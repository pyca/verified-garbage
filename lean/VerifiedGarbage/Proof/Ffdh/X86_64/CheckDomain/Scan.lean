module
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Parent

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Minus
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH domain validation on x86-64: significant bytes of q -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure Scanned (p : CdP) (s : State) : Prop where
  parent : Parent p s
  ep : word s.mem p.B (8 * sEp) = p.eqp
  el : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq

theorem scan_order {p : CdP} {s : State} (h : Parent p s) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (scan sQ)) s (StepPost p s (Scanned p)) := by
  have hl := h.base.qlen hq
  have hk := h.base.k1
  have hk' := h.base.k2
  have hn : p.qb ≠ [] := by intro he; simp [he] at hl; omega
  refine WP.mono (scan_ok h.outer (show sQ < 32 by decide) h.q
    (by rw [hl]; exact h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) hn
    (by rw [hl]; omega) ((h.base.dom.drop (2 * p.k)).take p.k)) fun t ⟨hep, hel, _, hf, k⟩ => ?_
  have hZ := h.good.2
  have hE := hdr_lt_slot p.w 8 (show sEl < 32 by decide)
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sEp sEl sFn at * <;> omega)
  have hh : ∀ i < 32, i ≠ sEp → i ≠ sEl → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi h1 h2 => hf.word_eq (fun r he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp only <;> omega) (by omega)
  have hb : Base p t := h.base.keep hi k (by
    intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide))
  have ho : Outer t p.B p.Z p.w := h.outer.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sEp sEl sFn at * <;> omega) k.2.2 (k.gpr (by decide))
  refine ⟨⟨⟨hb, ho, ?_, ?_⟩, hep, ?_⟩, hi, ?_, k.mono (by decide)⟩
  · rw [hh _ (by decide) (by decide) (by decide)]; exact h.g
  · rw [hh _ (by decide) (by decide) (by decide)]; exact h.q
  · simpa only [hl] using hel
  · intro i hi
    exact hh i (by omega) (by unfold sEp sFn; omega) (by unfold sEl sFn; omega)

theorem scanned_minus {p : CdP} {s : State} (h : Scanned p s) (ho : p.P % 2 = 1) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1) s
      (StepPost p s fun t => Scanned p t ∧ wv t.mem p.B (slot p.w aX) p.w = p.P - 1) :=
  WP.mono (minus_one h.parent ho) fun t ⟨⟨hp, hv, hh⟩, hi, hs, k⟩ =>
    ⟨⟨⟨hp, (hh _ (by decide)).trans h.ep, (hh _ (by decide)).trans h.el⟩, hv⟩, hi, hs, k⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
