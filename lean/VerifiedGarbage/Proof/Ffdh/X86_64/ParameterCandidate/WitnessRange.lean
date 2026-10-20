module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessRange
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter candidates on x86-64: the exact uniform witness interval -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG.Proof.Ffdh.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem witnessRange_ok {s : State} {B : Addr} {Z w N a : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w) (ho : N % 2 = 1)
    (ha : wv s.mem B (slot w aXm) w = a) :
    WP isa witnessRange s fun t =>
      t.gpr .rax = bit (2 ≤ a ∧ a < N - 1) ∧ t.zf = some (!decide (2 ≤ a ∧ a < N - 1)) ∧
      ModulusReady t B Z w mi N ∧ wv t.mem B (slot w aXm) w = a ∧
      Frm B [(slot w aTmp, 8 * w), (8 * VG.Impl.Ffdh.X86_64.Domain.sF, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hw : w < 2 ^ 31 := by have := hd.w128; omega
  have hP : (1 < wv s.mem B (slot w aXm) w ∧
      2 * (wv s.mem B (slot w aXm) w / 2) + 1 < wv s.mem B (slot w aN) w) ↔
      (2 ≤ a ∧ a < N - 1) := by
    rw [ha, h.n, VG.Proof.Ffdh.lt_pm1 ho]
    omega
  unfold witnessRange
  refine WP.mono (VG.Proof.Ffdh.X86_64.rangeTest_ok h.good hd.z (by have := hd.w4; omega) hw
    (a := aXm) (by decide) (by decide) h.one) fun t ⟨hax, hz, _, hf, k⟩ => ?_
  simp only [bit, propext hP] at hax hz ⊢
  refine ⟨hax, hz, h.of_frm hd hf k ((k.gpr (by decide)).trans h.good.rdi) ?_ ?_ ?_, ?_, hf, k⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    constructor
    · unfold slot hdrBytes aTmp; omega
    · decide
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
      VG.Impl.Ffdh.X86_64.Domain.sF]
    and_intros <;> rng_disj
  · simp only [VG.Impl.Ffdh.X86_64.Domain.sF]
    rng_disj
  · rw [hf.wv_eq (by simp only [VG.Impl.Ffdh.X86_64.Domain.sF]; rng_disj) (by
      have hb := slot_le (w := w) (show aXm < 8 by decide)
      have hn := h.good.scr.nowrap
      omega_using [hb, hd.z, hn])]
    exact ha

end VG.Proof.Ffdh.X86_64.ParameterCandidate
