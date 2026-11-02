module

import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.TimingTest
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Sieve
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.NoSp
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Environment
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.TimingFront
public import VerifiedGarbage.Proof.RsaKeyGen.MrCounts
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Spec.Dsa

/-! # The whole test leaks only what the contract releases -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86 VG.Impl.Mont.X86

theorem sieve_entry {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) : CandidateSieve.Entry E.sieveGeometry c (allocFrame 20 s) := by
  have pointer : s.gpr .edi = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    rw [L.input.scratch.edi_toNat, v.baseNat]
  refine ⟨sieve_context v L, ?_, ?_⟩
  · rw [allocFrame_gpr _ _ (by decide), pointer]; rfl
  · exact L.input.memory.symbol

theorem sieve_pair {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (large : 8161 < c) :
    RelCT isa (LoadedPair E c entropy) (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width)
      (Candidate.WithFlag (LoadedPair E c entropy)
        (Spec.RsaKeyGen.obviouslyComposite (64 * E.width) c)) := by
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) := v.stackFar _ List.mem_cons_self
  have tableFar : E.tableRegion.Disjoint (below E.p 136) := v.stackFar _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  intro s t tr ur u z P A B
  have trace := (CandidateSieve.code_trace v.sieve_valid (c := c) (d := c) (fun _ _ => rfl) rfl
    (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega)]; have := v.low; omega)
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    _ _ _ _ _ _ ⟨sieve_entry v P.1, sieve_entry v P.2⟩ A B).1
  obtain ⟨LU, flagU, _, _, _⟩ := wp_result (sieve_ok v P.1 large) A
  obtain ⟨LZ, flagZ, _, _, _⟩ := wp_result (sieve_ok v P.2 large) B
  exact ⟨trace, ⟨LU, LZ⟩, flagU, flagZ⟩

theorem LoadedPair.keepFlags {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t u z : State}
    (P : LoadedPair E c entropy s t) (U : Fupd s u) (Z : Fupd t z) : LoadedPair E c entropy u z :=
  ⟨(P.1.keepStack v (by rw [U.mem]; exact Frame.refl _ _) (U.keeps []) (by decide) (by decide)
      (by rw [U.syms])).1,
    (P.2.keepStack v (by rw [Z.mem]; exact Frame.refl _ _) (Z.keeps []) (by decide) (by decide)
      (by rw [Z.syms])).1⟩

theorem sieved_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (LoadedPair E c entropy)
      (VG.Impl.Dsa.X86.ProbablePrime.sieved E.bits montName mont roundName round) (fun _ _ => True) := by
  have shape := candidate_shape odd length (by have := v.bits.low; omega)
  have big : 2 ^ 63 ≤ 2 ^ (E.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := v.bits.low; omega)
  have space : 156 ≤ E.size := by have := v.header; omega
  have finishPair {s t : State} (P : LoadedPair E c entropy s t) : CandidateFinish.FinishPair E.base E.size s t :=
    ⟨P.1.input.scratch, P.2.input.scratch, P.1.input.usedPtr.trans P.2.input.usedPtr.symm⟩
  unfold VG.Impl.Dsa.X86.ProbablePrime.sieved
  cases composite : Spec.RsaKeyGen.obviouslyComposite (64 * E.width) c
  · have initial := sieve_pair v (c := c) (entropy := entropy) (by omega)
    rw [composite] at initial
    refine RelCT.seq initial (RelCT.seq ((Candidate.cmp_flag_trace false
      (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact Candidate.branch_false (test_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
      v odd length)
  · have initial := sieve_pair v (c := c) (entropy := entropy) (by omega)
    rw [composite] at initial
    refine RelCT.seq initial (RelCT.seq ((Candidate.cmp_flag_trace true
      (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact Candidate.branch_true ((CandidateFinish.used_trace space 2).mono (fun _ _ P => finishPair P)
      (fun _ _ _ => trivial))

theorem body_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (EntryPair E c entropy)
      (VG.Impl.Dsa.X86.ProbablePrime.body E.bits montName mont roundName round) (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (EntryPair E c entropy)
      (VG.Impl.Dsa.X86.ProbablePrime.body E.bits montName mont roundName round) (fun _ _ => True) := by
    unfold VG.Impl.Dsa.X86.ProbablePrime.body
    exact RelCT.seq (enter_trace v) (RelCT.seq (load_trace v odd)
      (sieved_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v odd length))
  refine ⟨(raw _ _ _ _ _ _ P A B).1, agree_regs ?_⟩
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  rw [Exec.gpr (body_noSp montNoSp roundNoSp E.bits montName roundName) A,
    Exec.gpr (body_noSp montNoSp roundNoSp E.bits montName roundName) B]
  exact P.1.sp.trans P.2.sp.symm

def FramedPair (E : Environment) (c : Nat) (entropy : List Byte) (s t : State) : Prop :=
  EntryPair E c entropy (Compact.entered s) (Compact.entered t) ∧ s.gpr .esp = t.gpr .esp

theorem framed_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (FramedPair E c entropy)
      (VG.Impl.Dsa.X86.ProbablePrime.code E.bits montName mont roundName round) (fun _ _ => True) := by
  have restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.Mont.X86.Compact.restoreRegs)
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  unfold VG.Impl.Dsa.X86.ProbablePrime.code
  apply VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := VG.X86.Taint.Agree (τr [.esp])) (fun _ _ P => P.2)
  exact (RelCT.seq (body_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v odd length)
    restore).mono (by rintro _ _ ⟨s, t, P, rfl, rfl⟩; exact P.1) (fun _ _ P => P)

end VG.Proof.Dsa.X86.ProbablePrime
