module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame

/-! # Preserved arguments around modulus preparation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64 VG.Proof.Ffdh.AArch64.ParameterCandidate

structure PrimeInput (P : PrimeParams) (used : Nat) (s : State) : Prop where
  ws : Ws s P.B P.Z P.w
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

theorem PrimeState.input {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeState P used s) : PrimeInput P used s :=
  ⟨h.ready.ws, h.ready.modulus, h.ptr, h.len, h.draw, h.rand, h.randLen, h.used, h.checks,
    h.source, h.writable⟩

theorem PrimeInput.advance {P : PrimeParams} {used : Nat} {s t : State}
    {rs : List (Nat × Nat)} (h : PrimeInput P used s)
    (hg : Ws t P.B P.Z P.w) (hn : wv t.mem P.B (slot P.w aN) P.w = P.N)
    (hf : Frm P.B rs s.mem t.mem) (hk : Keep mmRegs s t)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ P.Z)
    (hh : ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kUsed, kChecks], ∀ r ∈ rs,
      8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k) : PrimeInput P used t := by
  have hword : ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kUsed, kChecks],
      word t.mem P.B (8 * k) = word s.mem P.B (8 * k) := by
    intro k hmem
    have hk32 : k < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hf.word_eq (hh k hmem) (by omega)
  refine ⟨hg, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hword kOut (by simp)).trans h.ptr
  · exact (hword kUsedP (by simp)).trans h.len
  · exact (hword kLen (by simp)).trans h.draw
  · exact (hword kRand (by simp)).trans h.rand
  · exact (hword kRandLen (by simp)).trans h.randLen
  · exact (hword kUsed (by simp)).trans h.used
  · exact (hword kChecks (by simp)).trans h.checks
  · exact source_of_work h.source (extra := []) hf.work hr (by simp) P.randMax hk
  · intro i hi; rw [hk.wr]; exact h.writable i hi

theorem primeInputSetup_ok (M : Mont) {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeInput P used s) (hw : P.w ≤ 48) :
    WP isa (Impl.Dsa.AArch64.Generation.primeSetup M.mm) s fun t =>
      PrimeState P used t ∧ Frm P.B (modulusRanges P.w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (primeSetup_ok M h.ws hw P.exponentRoom h.n P.odd (by have := P.n3; omega))
    fun t ⟨ht, hf, hk⟩ => ?_
  have hi := h.advance ht.ws ht.modulus hf hk (by
    intro r hr
    have hroom := P.room
    simp only [modulusRanges, mpRanges, mpTail, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;>
      simp only [slot, hdrBytes, aOne, aAcc, aTmp, aR2, aY, aR1, aRm1, aE, sMinv, sCnt, sFn] at hroom ⊢ <;> omega_arith)
    (by
      intro k hmem r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      simp only [modulusRanges, mpRanges, mpTail, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;>
          simp only [slot, hdrBytes, aOne, aAcc, aTmp, aR2, aY, aR1, aRm1, aE,
            sMinv, sCnt, sFn, kOut, kUsedP, kLen, sK, kRand, kRandLen, kUsed, kChecks, kE] <;> omega_arith)
  exact ⟨⟨ht, hi.ptr, hi.len, hi.draw, hi.rand, hi.randLen, hi.used, hi.checks, hi.source, hi.writable⟩, hf, hk⟩

end VG.Proof.Dsa.AArch64.Generation
