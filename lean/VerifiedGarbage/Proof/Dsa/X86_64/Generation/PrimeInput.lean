module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeSetup

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetup
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame

/-! # Preserved arguments around modulus preparation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

structure PrimeInput (P : PrimeParams) (mi : BitVec 64) (used : Nat) (s : State) : Prop where
  good : Good s P.B P.Z P.w mi
  n : wv s.mem P.B (slot P.w aN) P.w = P.N
  ptr : word s.mem P.B (8 * kOut) = P.p
  len : word s.mem P.B (8 * kUsedP) = BitVec.ofNat 64 P.len
  draw : word s.mem P.B (8 * kLen) = BitVec.ofNat 64 P.drawBytes
  rand : word s.mem P.B (8 * kRand) = P.rp
  randLen : word s.mem P.B (8 * kRandLen) = BitVec.ofNat 64 P.rand.length
  used : word s.mem P.B (8 * kUsed) = BitVec.ofNat 64 used
  checks : word s.mem P.B (8 * kChecks) = BitVec.ofNat 64 P.checks
  source : Src s P.B P.Z P.rp P.rand
  writable : ∀ i < P.len, InRegions s.wr (off P.p i) 1
  stack : s.gpr .rsp = P.sp

theorem PrimeState.input {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) : PrimeInput P mi used s :=
  ⟨h.ready.good, h.ready.n, h.ptr, h.len, h.draw, h.rand, h.randLen, h.used, h.checks,
    h.source, h.writable, h.stack⟩

theorem PrimeInput.advance {P : PrimeParams} {mi mi' : BitVec 64} {used : Nat} {s t : State}
    {rs : List (Nat × Nat)} (h : PrimeInput P mi used s)
    (hg : Good t P.B P.Z P.w mi') (hn : wv t.mem P.B (slot P.w aN) P.w = P.N)
    (hf : Frm P.B rs s.mem t.mem) (hk : Keep mmRegs s t)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ P.Z)
    (hh : ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kUsed, kChecks], ∀ r ∈ rs,
      8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k) : PrimeInput P mi' used t := by
  have hword : ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kUsed, kChecks],
      word t.mem P.B (8 * k) = word s.mem P.B (8 * k) := by
    intro k hmem
    have hk32 : k < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hf.word_eq (hh k hmem) (by omega)
  refine ⟨hg, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hword kOut (by simp)).trans h.ptr
  · exact (hword kUsedP (by simp)).trans h.len
  · exact (hword kLen (by simp)).trans h.draw
  · exact (hword kRand (by simp)).trans h.rand
  · exact (hword kRandLen (by simp)).trans h.randLen
  · exact (hword kUsed (by simp)).trans h.used
  · exact (hword kChecks (by simp)).trans h.checks
  · exact source_of_work h.source (extra := []) hf.work hr (by simp) P.randMax hk
  · intro i hi; rw [hk.2.2]; exact h.writable i hi
  · exact (hk.gpr (by decide)).trans h.stack

theorem primeInputSetup_ok (M : Mont) {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeInput P mi used s) (hw : P.w ≤ 48) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSetup M.mm) s fun t =>
      ∃ mi', PrimeState P mi' used t ∧ Frm P.B (modulusRanges P.w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (primeSetup_ok M h.good P.dims h.n P.odd (by have := P.n3; omega) hw)
    fun t ⟨mi', ht, hf, hk⟩ => ?_
  have hi := h.advance ht.good ht.n hf hk (by
    have hroom := P.room
    simp only [modulusRanges, prepareRanges, constantRanges, r2Ranges, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros <;>
      simp only [slot, hdrBytes, aAcc, aTmp, aOne, aR2, aY, aR1, aRm1, aE, sMinv, sCnt, sFn] at hroom ⊢ <;> omega_using [hroom])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [modulusRanges, prepareRanges, constantRanges, r2Ranges, List.cons_append, List.nil_append, sCnt] <;> rng_disj)
  exact ⟨mi', ⟨ht, hi.ptr, hi.len, hi.draw, hi.rand, hi.randLen, hi.used, hi.checks,
    hi.source, hi.writable, hi.stack⟩, hf, hk⟩

end VG.Proof.Dsa.X86_64.Generation
