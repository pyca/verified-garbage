module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSatisfiable
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBody
import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpCode
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpWords
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABISeparate
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentStageTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateScheduleContinue
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRtTiming
import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClear
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateClearInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEntry
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
/-! # Native candidate generation has complete correctness, timing, and satisfiability certificates -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateSaved.lean`, which only this module imported.
section

/-! # Candidate workspace writes and nested frames retain the saved cdecl registers -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem saved_stack_far {E : Environment} (v : E.Valid) :
    (⟨E.p.setWidth 64, 16⟩ : Region).Disjoint (below E.p 136) := by
  unfold below
  rw [Taint.sub_setWidth v.low]
  exact Offset.base_disjoint_below _ (by decide)

theorem saved_read {E : Environment} (v : E.Valid) {s t : State}
    (fit : 16 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (F : MutableFrame E (Compact.entered s).mem t.mem) {i : Nat} (index : i < 4) :
    t.mem.readW (addr E.p (4 * i)) 32 = s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  have pFit : E.p.toNat + 16 ≤ 2 ^ 32 := by
    rw [← sp, Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat fit]
    have := (s.gpr .esp).isLt
    omega
  have same := F.readW (r := (⟨E.p.setWidth 64, 16⟩ : Region)) (a := addr E.p (4 * i)) (w := 32)
    (by rw [addr_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega)) (by
      intro r mem
      rcases List.mem_append.mp mem with mem | mem
      · exact (v.savedFar r (List.mem_append_left _ mem)).symm
      · obtain rfl := List.mem_singleton.mp mem
        exact saved_stack_far v) (by decide)
  have word := pushed_word (rs := Compact.savedRegisters) (by decide) fit index
  change (Compact.entered s).mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 = _ at word
  rw [sp] at word
  exact same.trans word

theorem return_read {E : Environment} (_v : E.Valid) {s t : State}
    (fit : 152 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (returnFar : ∀ r ∈ E.writeRegions, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r)
    (F : MutableFrame E (Compact.entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have outside : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 152) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.base_disjoint_below _ (by decide)
  have inner : (below E.p 136).Sub (below (s.gpr .esp) 152) := by
    rw [← sp, Compact.entered, pushed_esp]
    exact below_inner (by decide) fit
  have same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4) (by
    intro r mem
    rcases List.mem_append.mp mem with mem | mem
    · exact returnFar r mem
    · obtain rfl := List.mem_singleton.mp mem
      exact outside.sub_right inner) (by decide)
  have pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) (by change 16 ≤ _; omega)
  exact same.trans (pushed.readW (Region.contains_self _ _) (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem
    exact outside.sub_right (below_sub (by decide) fit)) (by decide))

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFrameResult.lean`, which only this module imported.
section

/-! # The complete candidate restores the native calling convention after every result -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem StepOutputs.keep {E : Environment} {entropy : List Byte}
    {result : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand)} {s t : State}
    (R : StepOutputs E entropy result s) (eax : t.gpr .eax = s.gpr .eax) (mem : t.mem = s.mem) :
    StepOutputs E entropy result t := by
  cases result with
  | none => simpa only [StepOutputs, Outputs, eax, mem] using R
  | some pr =>
    obtain ⟨candidate, rest⟩ := pr
    cases candidate <;> simpa only [StepOutputs, Outputs, eax, mem] using R

theorem framed_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : EntryInput E eBytes pBytes entropy (Compact.entered s))
    (fit : 152 ≤ (s.gpr .esp).toNat)
    (returnFar : ∀ r ∈ E.writeRegions, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) s fun t =>
      abiPreserved s t ∧ StepOutputs E entropy (Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy) t := by
  have savedFit : 16 ≤ (s.gpr .esp).toNat := by omega
  have entrySp := I.arguments.sp
  have inner : NoSp (.seq (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) (.block Compact.restoreRegs)) :=
    CandidateNoSp.sequence (CandidateNoSp.body montNoSp roundNoSp montName roundName) (NoSp.of_all (by rfl))
  unfold VG.Impl.RsaKeyGen.X86.Candidate.code
  refine WP.frame (rs := VG.Proof.Mont.X86.Compact.savedRegisters) (by decide) (by decide) (by decide) savedFit inner ?_
  refine WP.seq (WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v I)
    fun t ⟨R, F, K⟩ => ?_)
  have sp : t.gpr .esp = E.p := (K.1 .esp (by unfold bodyClob; decide)).trans entrySp
  have pFit : E.p.toNat + 16 ≤ 2 ^ 32 := by
    rw [← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat savedFit]
    have := (s.gpr .esp).isLt
    omega
  have read (i : Nat) (index : i < 4) : readSrc t (.mem (at_ .esp (4 * i))) = some
      (s.gpr (VG.Proof.Mont.X86.Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp]
      change InRegions (s.rd ++ (below (s.gpr .esp) 16 :: s.wr)) (addr E.p (4 * i)) 4
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      have region : below (s.gpr .esp) 16 = ⟨E.p.setWidth 64, 16⟩ := by
        rw [← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
        rfl
      rw [region, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, sp, saved_read v savedFit entrySp F index]
  refine WP.mono (VG.Proof.Mont.X86.Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro u ⟨edi, esi, ebp, mem, keep⟩
  have sp' : u.gpr .esp = E.p := (keep.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show VG.Proof.Mont.X86.Compact.savedRegisters.length = 4 from rfl,
        VG.Proof.Mont.X86.Compact.popped_four_value, sp', mem]
      exact saved_read v savedFit entrySp F (by decide : 3 < 4)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', ← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]
    exact return_read v fit entrySp returnFar F
  · apply R.keep
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact keep.1 .eax (by decide)
    · rw [popped_mem, mem]

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateCorrect.lean`, which only this module imported.
section

/-! # The complete native candidate satisfies the shared RSA generation contract -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem correct {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) s trace t ∧
      abiPreserved s t ∧ contract.post s t := by
  have A := call_layout h
  have D := call_separation h
  obtain ⟨trace, t, run, preserved, R⟩ := framed_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    (call_valid h) (entry_input h) A.low D.returnFar
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  rw [BitVec.setWidth_append_eq_right]
  have entropyLength : (callEntropy s).length = (arg s 8).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  change StepOutputs (callEnvironment s) (callEntropy s)
    (Spec.RsaKeyGen.candidateOp (arg s 1).toNat (callEBytes s) (callPBytes s) (callEntropy s)) t at R
  cases result : Spec.RsaKeyGen.candidateOp (arg s 1).toNat (callEBytes s) (callPBytes s) (callEntropy s) with
  | none =>
    rw [result] at R
    dsimp only [callEBytes, callPBytes, callEntropy] at result
    rw [result]
    obtain ⟨status, bytes, used⟩ := R
    refine ⟨by rw [status]; rfl, bytes, ?_⟩
    simpa only [callEnvironment, Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.map_append, List.map_nil,
      List.map_cons, List.nil_append, Nat.mul_zero, BitVec.add_zero] using congrArg (fun x => [x]) used
  | some pr =>
    obtain ⟨candidate, rest⟩ := pr
    rw [result] at R
    cases candidate
    all_goals dsimp only [StepOutputs, Outputs] at R
    all_goals obtain ⟨status, bytes, used⟩ := R
    all_goals rw [entropyLength] at used
    all_goals dsimp only [callEBytes, callPBytes, callEntropy] at result
    all_goals rw [result]
    all_goals refine ⟨by rw [status]; rfl, bytes, ?_⟩
    all_goals simpa only [callEnvironment, Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.map_append, List.map_nil,
      List.map_cons, List.nil_append, Nat.mul_zero, BitVec.add_zero] using congrArg (fun x => [x]) used

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidatePublic.lean`, which only this module imported.
section

/-! # The shared contract publishes arguments, table address, exponent bytes, and only its declared candidate leak -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.RsaKeyGen

structure PublicInputs (s t : State) : Prop where
  stack : s.gpr .esp = t.gpr .esp
  arguments : ∀ i < 11, arg s i = arg t i
  tables : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol
  observations : (callEBytes s).map (·.toNat) ++
      Spec.RsaKeyGen.candidateLeak (arg s 1).toNat (callEBytes s) (callPBytes s) (callEntropy s) =
    (callEBytes t).map (·.toNat) ++
      Spec.RsaKeyGen.candidateLeak (arg t 1).toNat (callEBytes t) (callPBytes t) (callEntropy t)

theorem public_inputs {s t : State} (H : contract.pub s t) : PublicInputs s t := by
  sig_pub [contract, Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  sig_split H
  refine ⟨by with_reducible assumption, ?_, by with_reducible assumption, by dsimp only [callEBytes, callPBytes, callEntropy]; with_reducible assumption⟩
  intro i index
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem PublicInputs.table {s t : State} (P : PublicInputs s t) :
    s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol := by
  exact P.tables

theorem PublicInputs.environment {s t : State} (P : PublicInputs s t) : callEnvironment s = callEnvironment t := by
  simp only [callEnvironment, P.arguments 0 (by decide), P.arguments 1 (by decide), P.arguments 2 (by decide),
    P.arguments 3 (by decide), P.arguments 4 (by decide), P.arguments 5 (by decide), P.arguments 6 (by decide),
    P.arguments 7 (by decide), P.arguments 8 (by decide), P.arguments 9 (by decide), P.arguments 10 (by decide),
    P.stack, P.table]

theorem PublicInputs.exponent {s t : State} (P : PublicInputs s t) : callEBytes s = callEBytes t := by
  have lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    simp only [List.length_map, callEBytes, VG.Proof.Bignum.bytesAt_length, P.arguments 4 (by decide)]
  exact map_toNat_inj (List.append_inj P.observations lengths).1

theorem PublicInputs.leak {s t : State} (P : PublicInputs s t) :
    SameLeak (callEnvironment s) (callEBytes s) (callPBytes s) (callPBytes t) (callEntropy s) (callEntropy t) := by
  have lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    simp only [List.length_map, callEBytes, VG.Proof.Bignum.bytesAt_length, P.arguments 4 (by decide)]
  have L := (List.append_inj P.observations lengths).2
  rw [← P.arguments 1 (by decide), ← P.exponent] at L
  exact L

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateAvailableTiming.lean`, which only this module imported.
section

/-! # The candidate's front and its continuation hide the entropy -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

theorem four_comparison (x : BitVec 32) : (x - 4 == 0#32) = decide (x = 4) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

theorem FrontPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : FrontPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    FrontPair E eBytes pBytes qBytes rBytes sBytes u z := by
  rcases P with ⟨same, other⟩ | ⟨S, T, D, rest⟩
  · exact Or.inl ⟨by rw [U.gpr, Z.gpr]; exact same, by rw [U.gpr]; exact other⟩
  · exact Or.inr ⟨by rw [U.gpr]; exact S, by rw [Z.gpr]; exact T, D.keepFlags v U Z, rest⟩

/-- `eax = 4` decides the continuation in both runs alike. -/
theorem continue_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (FrontPair E eBytes pBytes qBytes rBytes sBytes)
      (.seq (.block [.alu .cmp .eax (.imm 4)])
        (.ite .e (VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck montName mont roundName round) (.block [])))
      (fun _ _ => True) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block [.alu .cmp .eax (.imm 4)])
      (VG.X86.Taint.Agree (τr [])) := checkedBlockInvariant rfl rfl
  have cmp : RelCT isa (FrontPair E eBytes pBytes qBytes rBytes sBytes) (.block [.alu .cmp .eax (.imm 4)])
      (fun u z => FrontPair E eBytes pBytes qBytes rBytes sBytes u z ∧
        isa.eval .e u = some (decide (u.gpr .eax = 4)) ∧ isa.eval .e z = some (decide (z.gpr .eax = 4))) := by
    intro s t tr ur u z P A B
    obtain ⟨U, ZU⟩ := wp_result (compare_value_ok (s := s) 4) A
    obtain ⟨Z, ZZ⟩ := wp_result (compare_value_ok (s := t) 4) B
    refine ⟨(raw _ _ _ _ _ _ (agree_regs (by intro r mem; cases mem)) A B).1, P.keepFlags v U Z, ?_, ?_⟩
    · rw [ZU, U.gpr, four_comparison]
    · rw [ZZ, Z.gpr, four_comparison]
  refine RelCT.seq cmp (VG.RelCT.ite ?_ ?_ ?_)
  · rintro u z ⟨P, CU, CZ⟩
    rw [CU, CZ]
    rcases P with ⟨same, _⟩ | ⟨S, T, _⟩
    · rw [same]
    · rw [S, T]
  · rintro s t tr ur u z ⟨⟨P, CU, _⟩, yes⟩ A B
    rw [CU] at yes
    have four : s.gpr .eax = 4 := of_decide_eq_true (Option.some.inj yes)
    rcases P with ⟨_, other⟩ | ⟨_, _, D, rClose, sClose, rComposite, sComposite⟩
    · exact absurd four other
    have schedules := schedule_eq v length rEnough leak
    exact exponent_stage_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough
      (schedule_gcd_eq schedules rClose sClose rComposite sComposite)
      (schedule_shape_eq schedules rClose sClose rComposite sComposite) _ _ _ _ _ _ D A B
  · have empty : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block []) (VG.X86.Taint.Agree (τr [])) :=
      checkedBlockInvariant rfl rfl
    exact empty.mono (fun _ _ _ => agree_regs (by intro r mem; cases mem)) (fun _ _ _ => trivial)

theorem available_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.available
  exact RelCT.seq (front_rt_trace v length rEnough enough leak)
    (continue_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length rEnough enough leak)

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateClearTiming.lean`, which only this module imported.
section

/-! # Clearing leaks only the public output address and length -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateClear
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateClear

theorem args_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (header : 8 ≤ size) :
    WP isa (.block args) s fun t =>
      t.gpr .esi = s.mem.readW (off base 0) 32 ∧ t.gpr .ecx = s.mem.readW (off base 4) 32 := by
  unfold args
  refine wp_movS (readSrc_sc S (d := 0) (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 4) (by omega)) fun b B _ =>
    wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.other .esi (by decide), B.other .esi (by decide), A.gpr],
    by rw [T.other .ecx (by decide), B.gpr, A.mem]⟩

def InputPair (base : Addr) (size : Nat) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧
    s.mem.readW (off base 0) 32 = t.mem.readW (off base 0) 32 ∧
    s.mem.readW (off base 4) 32 = t.mem.readW (off base 4) 32

theorem args_trace {base : Addr} {size : Nat} (header : 8 ≤ size) :
    RelCT isa (InputPair base size) (.block args) (VG.X86.Taint.Agree (τr [.esi, .ecx])) := by
  intro s t tr ur u z ⟨S, T, outEq, lenEq⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block args)
      (VG.X86.Taint.Agree (τr [.edi])) := checkedBlockInvariant rfl rfl
  have A : VG.X86.Taint.Agree (τr [.edi]) s t := by
    apply agree_regs
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  have trace := (raw _ _ _ _ _ _ A E G).1
  obtain ⟨outU, lenU⟩ := wp_result (args_ok S header) E
  obtain ⟨outZ, lenZ⟩ := wp_result (args_ok T header) G
  refine ⟨trace, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · rw [outU, outZ]; exact outEq
  · rw [lenU, lenZ]; exact lenEq

theorem code_trace {base : Addr} {size : Nat} (header : 8 ≤ size) :
    RelCT isa (InputPair base size) code (fun _ _ => True) := by
  unfold code
  refine RelCT.seq (args_trace header) ?_
  apply RelCT.taint (A := taint) (τr [.esi, .ecx]) (fun _ _ H => H)
    (hc := VG.Taint.hintOf taint (τr [.esi, .ecx]) (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne))
  rfl

end VG.Proof.RsaKeyGen.X86.CandidateClear
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFrontTiming.lean`, which only this module imported.
section

/-! # The candidate's output clearing and entropy guard have a public trace -/

section
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
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
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
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateEntryTiming.lean`, which only this module imported.
section

/-! # Argument entry leaks only the public cdecl arguments and workspace address -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateArgs

def EntryPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Entry base size p inputs s ∧ Entry base size p inputs t

theorem pointer_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (S : Entry base size p inputs s) :
    WP isa (.block [.mov .edi (.mem (arg 9))]) s fun t => t.gpr .edi = inputs 9 ∧ Keeps [.edi] s t := by
  refine wp_movS (S.read 9 (by decide)) fun t T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem pointer_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) (.block [.mov .edi (.mem (arg 9))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (arg 9))])
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  have A : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.sp.trans T.sp.symm)
  obtain ⟨ptrU, Ku⟩ := wp_result (pointer_ok S) E
  obtain ⟨ptrZ, Kz⟩ := wp_result (pointer_ok T) G
  refine ⟨(raw _ _ _ _ _ _ A E G).1, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · rw [Ku.1 .esp (by decide), Kz.1 .esp (by decide)]; exact S.sp.trans T.sp.symm
  · exact ptrU.trans ptrZ.symm

def InitializedPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Context base size p inputs s ∧ Context base size p inputs t ∧
    (∀ i < 11, s.mem.readW (off base (4 * i)) 32 = inputs i ∧ t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
    s.mem.readW (off base 44) 32 = inputs 2 ∧ t.mem.readW (off base 44) 32 = inputs 2

theorem enter_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) enter (InitializedPair base size p inputs) := by
  have copied : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) code (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ H => H)
      (hc := VG.Taint.hintOf taint (τr [.esp, .edi]) code)
    kernel_rfl
  have raw : RelCT isa (EntryPair base size p inputs) enter (fun _ _ => True) := RelCT.seq pointer_trace copied
  intro s t tr ur u z ⟨S, T⟩ E G
  obtain ⟨Cu, valuesU, usedU, _, _⟩ := wp_result (enter_ok S) E
  obtain ⟨Cz, valuesZ, usedZ, _, _⟩ := wp_result (enter_ok T) G
  exact ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1, Cu, Cz, fun i index => ⟨valuesU i index, valuesZ i index⟩, usedU, usedZ⟩

end VG.Proof.RsaKeyGen.X86.CandidateArgs
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateBodyTiming.lean`, which only this module imported.
section

/-! # Native argument entry and the complete candidate body obey the declared leak -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure BodyPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop where
  left : EntryInput E eBytes pBytes rBytes s
  right : EntryInput E eBytes qBytes sBytes t

theorem enter_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (BodyPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.CandidateArgs.enter
      (InputPair E eBytes pBytes qBytes rBytes sBytes) := by
  intro s t tr ur u z P A B
  have trace := (CandidateArgs.enter_trace _ _ _ _ _ _ ⟨P.left.arguments, P.right.arguments⟩ A B).1
  obtain ⟨IU, _, _⟩ := wp_result (enter_input_ok v P.left) A
  obtain ⟨IZ, _, _⟩ := wp_result (enter_input_ok v P.right) B
  exact ⟨trace, IU, IZ⟩

theorem body_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (BodyPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (BodyPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) (fun _ _ => True) :=
    RelCT.seq (enter_pair_trace v) (front_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
      P.left.memory.entropyLength P.right.memory.entropyLength leak)
  refine ⟨(raw _ _ _ _ _ _ P A B).1, agree_regs ?_⟩
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  rw [Exec.gpr (CandidateNoSp.body montNoSp roundNoSp montName roundName) A,
    Exec.gpr (CandidateNoSp.body montNoSp roundNoSp montName roundName) B]
  exact P.left.arguments.sp.trans P.right.arguments.sp.symm

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFrameTiming.lean`, which only this module imported.
section

/-! # Saving and restoring cdecl registers preserves candidate trace equivalence -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def FramedPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop :=
  BodyPair E eBytes pBytes qBytes rBytes sBytes (Compact.entered s) (Compact.entered t) ∧ s.gpr .esp = t.gpr .esp

theorem framed_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (FramedPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) (fun _ _ => True) := by
  have restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.Mont.X86.Compact.restoreRegs)
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  unfold VG.Impl.RsaKeyGen.X86.Candidate.code
  apply VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := VG.X86.Taint.Agree (τr [.esp])) (fun _ _ P => P.2)
  exact (RelCT.seq (body_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v leak) restore).mono
    (by rintro _ _ ⟨s, t, P, rfl, rfl⟩; exact P.1) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateConstantTime.lean`, which only this module imported.
section

/-! # Native candidate generation is constant time under exactly the shared contract's declared leak -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem constantTime {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) :
    ConstantTime isa contract.pre contract.pub (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) := by
  apply RelCT.constantTime
  intro s t tr ur u z ⟨HS, HT, HP⟩ A B
  have P := public_inputs HP
  have I := entry_input HS
  have J := entry_input HT
  rw [← P.environment, ← P.exponent] at J
  exact framed_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
    (call_valid HS) P.leak _ _ _ _ _ _ ⟨⟨I, J⟩, P.stack⟩ A B

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem verified {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) :
    Verified target (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) contract :=
  ⟨correct montVerified montNoSp montStack roundVerified roundNoSp roundStack,
    constantTime montVerified montNoSp montStack roundVerified roundNoSp roundStack, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.Candidate
