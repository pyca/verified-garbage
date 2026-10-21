module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrimeExport
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishInput

/-! # Prime export and its entropy count have a trace independent of the prime -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

structure PrimePair (E : Environment) (c d : Nat) (s t : State) : Prop where
  left : FinishReady E c s
  right : FinishReady E d t
  stack : s.gpr .esp = t.gpr .esp

structure StorePair (E : Environment) (c d : Nat) (s t : State) : Prop extends PrimePair E c d s t where
  outLeft : s.gpr .ebx = E.out
  outRight : t.gpr .ebx = E.out
  lengthLeft : s.gpr .ecx = BitVec.ofNat 32 (8 * E.width)
  lengthRight : t.gpr .ecx = BitVec.ofNat 32 (8 * E.width)

theorem PrimePair.agree {E : Environment} {c d : Nat} {s t : State} (P : PrimePair E c d s t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact P.stack
  · exact BitVec.eq_of_toNat_eq (P.left.1.scratch.edi_toNat.trans P.right.1.scratch.edi_toNat.symm)

theorem primeArgs_trace {E : Environment} (v : E.Valid) {c d : Nat} :
    RelCT isa (PrimePair E c d) (.block CandidateFinish.primeArgs) (StorePair E c d) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block CandidateFinish.primeArgs)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  have space : 8 ≤ E.size := by have H : 256 ≤ E.size := v.geometry.headerFit; omega
  obtain ⟨outU, lenU, memU, KU⟩ := wp_result (CandidateFinish.primeArgs_ok P.left.1.scratch space) A
  obtain ⟨outZ, lenZ, memZ, KZ⟩ := wp_result (CandidateFinish.primeArgs_ok P.right.1.scratch space) B
  refine ⟨(raw _ _ _ _ _ _ P.agree A B).1, ⟨P.left.keepMem memU KU (by decide) (by decide),
    P.right.keepMem memZ KZ (by decide) (by decide), ?_⟩, outU.trans P.left.1.outEq,
    outZ.trans P.right.1.outEq, lenU.trans P.left.1.lengthEq, lenZ.trans P.right.1.lengthEq⟩
  rw [KU.1 .esp (by decide), KZ.1 .esp (by decide)]
  exact P.stack

theorem export_trace {E : Environment} {c d : Nat} :
    RelCT isa (StorePair E c d) (VG.Impl.Bignum.X86.storeBE (VG.Impl.Bignum.X86.PublicContext.slot E.width 0))
      (CandidateFinish.FinishPair E.base E.size) := by
  intro s t tr ur u z P A B
  have agree : VG.X86.Taint.Agree storeTaint s t := by
    apply agree_regs
    intro r mem
    change r ∈ [.edi, .esp, .ebx, .ecx] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl
    · exact BitVec.eq_of_toNat_eq (P.left.1.scratch.edi_toNat.trans P.right.1.scratch.edi_toNat.symm)
    · exact P.stack
    · exact P.outLeft.trans P.outRight.symm
    · exact P.lengthLeft.trans P.lengthRight.symm
  obtain ⟨SU, ptrU, _⟩ := wp_result (CandidateFinish.export_header_ok P.left.1 P.outLeft P.lengthLeft) A
  obtain ⟨SZ, ptrZ, _⟩ := wp_result (CandidateFinish.export_header_ok P.right.1 P.outRight P.lengthRight) B
  exact ⟨(storeBE_relCT _ _ _ _ _ _ _ agree A B).1, SU, SZ, ptrU.trans ptrZ.symm⟩

theorem prime_trace {E : Environment} (v : E.Valid) {c d : Nat} :
    RelCT isa (PrimePair E c d) (VG.Impl.RsaKeyGen.X86.CandidateFinish.prime E.width) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateFinish.prime
  exact RelCT.seq (primeArgs_trace v) (RelCT.seq export_trace
    (CandidateFinish.used_trace (by have H : 256 ≤ E.size := v.geometry.headerFit; omega) 1))

end VG.Proof.RsaKeyGen.X86.Candidate
