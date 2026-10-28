module

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentStageTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateScheduleContinue
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRtTiming

/-! # The candidate's front and its continuation hide the entropy -/

@[expose] public section
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
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
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
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
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
