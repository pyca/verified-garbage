module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateAvailableTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateClearTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateClearInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRtTiming

/-! # The candidate's output clearing and entropy guard have a public trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen
open VG.Impl.Mont.X86

theorem clear_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (InputPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.Candidate.clear
      (ClearedPair E eBytes pBytes qBytes rBytes sBytes) := by
  intro s t tr ur u z P A B
  have raw := CandidateClear.code_trace (base := E.base) (size := E.size)
    (by have H : 256 ≤ E.size := v.geometry.headerFit; omega)
  have trace := (raw _ _ _ _ _ _ ⟨P.left.scratch, P.right.scratch,
    P.left.out_eq.trans P.right.out_eq.symm, (P.left.header 1 (by decide)).trans (P.right.header 1 (by decide)).symm⟩ A B).1
  obtain ⟨IU, zerosU, _, _⟩ := wp_result (clear_ok v P.left) A
  obtain ⟨IZ, zerosZ, _, _⟩ := wp_result (clear_ok v P.right) B
  exact ⟨trace, ⟨IU, IZ⟩, zerosU, zerosZ⟩

def guardArgs : List Instr := [.mov .eax (.mem (sc 32)), .alu .cmp .eax (.mem (sc 4))]

theorem guardArgs_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : WP isa (.block guardArgs) s fun t =>
      isa.eval .b t = some (decide (E.randLength < E.length)) ∧ t.mem = s.mem ∧ Keeps [.eax] s t ∧ t.syms = s.syms := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have lengthBound : E.length < 2 ^ 32 := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  unfold guardArgs
  refine wp_movS (readSrc_sc I.scratch (d := 32) (by omega)) fun a A _ =>
    WP.mono (cmp_src_cf (readSrc_sc (I.scratch.of_keeps A.keeps (by decide)) (d := 4) (by omega))) fun t ⟨T, CF⟩ => ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.widen (T.keeps []), T.syms.trans A.syms⟩
  change t.cf = _
  rw [CF, A.gpr, A.mem, I.header 8 (by decide), I.header 1 (by decide)]
  change some (decide ((BitVec.ofNat 32 E.randLength).toNat < (BitVec.ofNat 32 E.length).toNat)) = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.randLengthFit, Nat.mod_eq_of_lt lengthBound]

theorem guardArgs_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes) (.block guardArgs)
      (WithCondition (ClearedPair E eBytes pBytes qBytes rBytes sBytes) .b (decide (E.randLength < E.length))) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block guardArgs)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  obtain ⟨flagU, memU, KU, symU⟩ := wp_result (guardArgs_ok v P.left) A
  obtain ⟨flagZ, memZ, KZ, symZ⟩ := wp_result (guardArgs_ok v P.right) B
  exact ⟨(raw _ _ _ _ _ _ P.toInputPair.agree A B).1,
    P.keepMem v memU memZ KU KZ (by decide) (by decide) symU symZ, flagU, flagZ⟩

theorem front_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (rLength : rBytes.length = E.randLength) (sLength : sBytes.length = E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (InputPair E eBytes pBytes qBytes rBytes sBytes)
      (.seq VG.Impl.RsaKeyGen.X86.Candidate.clear (.seq (.block guardArgs)
        (.ite .b VG.Impl.RsaKeyGen.X86.CandidateFinish.none
          (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round)))) (fun _ _ => True) := by
  refine RelCT.seq (clear_pair_trace v) (RelCT.seq (guardArgs_trace v) ?_)
  by_cases enough : E.length ≤ E.randLength
  · have condition : decide (E.randLength < E.length) = false := decide_eq_false (by omega)
    rw [condition]
    exact branch_false (available_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
      (rLength.trans sLength.symm) (by rw [rLength]; exact enough) enough leak)
  · have condition : decide (E.randLength < E.length) = true := decide_eq_true (by omega)
    rw [condition]
    apply branch_true
    exact (CandidateFinish.none_trace (base := E.base) (size := E.size)
      (by have H : 256 ≤ E.size := v.geometry.headerFit; omega)).mono (fun _ _ P =>
        ⟨P.left.scratch, P.right.scratch, P.left.usedPointer.trans P.right.usedPointer.symm⟩) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.Candidate
