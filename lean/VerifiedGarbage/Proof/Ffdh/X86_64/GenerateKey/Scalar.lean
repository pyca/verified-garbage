module
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Finish
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
public import Mathlib.Tactic.TermCongr
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH on x86-64: the complete scalar-sampling stage -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem saved_scan {p : GkP} {s t : State} (hf : Frm p.B scanRanges s.mem t.mem) :
    ∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := by
  intro i hi
  exact hf.word_eq (by
    simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [sEp, sEl, sMsk, sFn] <;> omega) (by omega)

/-- The sampled scalar is ready for the existing private-key arithmetic proofs. -/
def ScalarPost (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  CheckPrivate.Base p.kp (p.xb rb) t ∧ Src t p.B p.Z p.xp (p.cut rb) ∧ t.gpr .rdi = p.B ∧
    word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep mmRegs s t

theorem scalar_ok {p : GkP} {rb : List Byte} {s : State} (h : Inputs p rb s) (hm : p.mv = true) :
    WP isa (seqs scalar) s (ScalarPost p rb s) := by
  unfold scalar
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.bound) (by simp [bound]) (by simp)
    (WP.mono (scan_inputs h) fun u ⟨hu, hn, ha, hf, k₁⟩ => ?_)
  change WP isa (.seq (.block smear) (.seq (.block cutSetup)
    (.seq (.loop (.block cutBody) .ne) (.block cutFinish)))) u _
  refine WP.seq (WP.mono (smear_inputs hu hn ha) fun v ⟨hv, hnv, hmask, hfv, k₂⟩ => ?_)
  refine WP.seq (WP.mono (cutSetup_ok hv hnv hmask) fun z ⟨⟨hr, hmz⟩, k₃⟩ => ?_)
  have hz : Inputs p rb z := hv.keep (by intro a _; rw [hmz]) k₃ (by decide)
  refine WP.seq (WP.mono (cut_inputs hz hr) fun a ⟨ha, hx, hh, h8, hf₄, k₄⟩ => ?_)
  have hna : word a.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n := by
    rw [hh _ (by have := ha.base.hZ; change 200 ≤ p.Z; omega), hmz]
    exact hnv
  refine WP.mono (finish_base ha hx hm hna h8) fun t ⟨hb, hd, hG, hQ, hs, hi, k₅⟩ => ?_
  refine ⟨hb, hx.congrK hi k₅, hd, hG, hQ, ?_, ?_, (((k₁.trans k₂).trans k₃).trans (k₄.trans k₅)).mono (by decide)⟩
  · intro i hi'
    rw [hs i hi', hh _ (by have := h.base.hZ; omega), hmz, saved_scan hfv i hi', saved_scan hf i hi']
  · have hZ : 256 ≤ p.Z := by have := h.base.hZ; omega
    have f₁ : RunFrame p s.mem u.mem := .of_frm hf (fun r hr => (scanRanges_end r hr).trans hZ)
    have f₂ : RunFrame p u.mem v.mem := .of_frm hfv (fun r hr => (scanRanges_end r hr).trans hZ)
    have f₃ : RunFrame p v.mem z.mem := by rw [hmz]; exact .refl _ _
    exact ((f₁.trans f₂).trans f₃).trans (hf₄.trans (.of_scr hi))

end VG.Proof.Ffdh.X86_64.GenerateKey
