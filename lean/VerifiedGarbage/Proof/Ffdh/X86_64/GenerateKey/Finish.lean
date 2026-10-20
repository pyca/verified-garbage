module
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutFinish
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH on x86-64: sampled inputs enter the proven private-scalar core -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The private-key core sees the significant slice of x and the initialized y. -/
theorem finish_base {p : GkP} {rb : List Byte} {s : State} (h : Inputs p rb s)
    (hx : Src s p.B p.Z p.xp (p.cut rb)) (hm : p.mv = true)
    (hn : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n) (h8 : s.gpr .r8 = BitVec.ofNat 64 p.ld) :
    WP isa (.block cutFinish) s fun t =>
      CheckPrivate.Base p.kp (p.xb rb) t ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧
      InScr p.B p.Z s.mem t.mem ∧ Keep [.rax] s t := by
  have hk := h.base.k1
  have hl := h.base.ld_lt
  have hZ := h.base.hZ
  refine WP.mono (cutFinish_ok h.base.scr h.rdi (by omega)
    (h.base.hdr (sX, p.xp) (by simp [GkP.headers])) hn h8)
    fun t ⟨hX, hXl, hf, k⟩ => ?_
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [sX, sXl, sFn] <;> omega)
  have hh : ∀ i < 32, i ≠ sX → i ≠ sXl → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hx hxl => hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> omega) (by omega)
  refine ⟨⟨h.base.k1, h.base.k2, h.base.dl, h.base.doml, List.length_replicate,
    h.base.xb_length, by change 1 ≤ p.k - p.ld; omega, by change p.k - p.ld ≤ p.k; omega,
    h.base.hZ, h.base.scr.congr k.2.2, h.base.dom.congrK hi k,
    (hx.drop p.ld).congrK hi k, h.y.congrK hi k, ?_, ?_⟩,
    (k.gpr (by decide)).trans h.rdi,
    (hh _ (by decide) (by decide) (by decide)).trans h.g,
    (hh _ (by decide) (by decide) (by decide)).trans h.q,
    fun i hi => hh i (by omega) (by unfold sX sFn; omega) (by unfold sXl sFn; omega), hi, k⟩
  · intro e he
    simp only [CheckPrivate.KpP.headers, GkP.kp, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hh sDom (by decide) (by decide) (by decide)).trans
        (h.base.hdr (sDom, p.dp) (by simp [GkP.headers]))
    · exact (hh sDomLen (by decide) (by decide) (by decide)).trans
        (h.base.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [GkP.headers]))
    · exact (hh sK (by decide) (by decide) (by decide)).trans
        (h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers]))
    · exact (hh sY (by decide) (by decide) (by decide)).trans
        (h.base.hdr (sY, p.yp) (by simp [GkP.headers]))
    · exact hX
    · exact hXl
  · change Spec.Ffdh.privateValid p.params (Spec.Rsa.os2ip (p.xb rb)) = p.sv
    rw [h.base.sample_value hm]
    exact h.base.valid

end VG.Proof.Ffdh.X86_64.GenerateKey
