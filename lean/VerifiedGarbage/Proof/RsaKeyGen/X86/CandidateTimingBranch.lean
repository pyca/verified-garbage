module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Boolean status branches compose without publishing candidate arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def WithFlag (P : State → State → Prop) (bit : Bool) (s t : State) : Prop :=
  P s t ∧ s.gpr .eax = BitVec.ofNat 32 bit.toNat ∧ t.gpr .eax = BitVec.ofNat 32 bit.toNat

def WithCondition (P : State → State → Prop) (c : Cond) (bit : Bool) (s t : State) : Prop :=
  P s t ∧ isa.eval c s = some bit ∧ isa.eval c t = some bit

theorem DrawnPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : DrawnPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    DrawnPair E eBytes pBytes qBytes rBytes sBytes u z :=
  ⟨P.left.keepMem v U.mem (U.keeps []) (by decide) (by decide) U.syms,
    P.right.keepMem v Z.mem (Z.keeps []) (by decide) (by decide) Z.syms⟩

theorem TestPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : TestPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    TestPair E eBytes pBytes qBytes rBytes sBytes u z := by
  refine ⟨P.toDrawnPair.keepFlags v U Z, ?_, ?_⟩
  · rw [U.mem]; exact P.savedLeft
  · rw [Z.mem]; exact P.savedRight

theorem cmp_flag_trace {P : State → State → Prop} (bit : Bool)
    (keep : ∀ s t u z, P s t → Fupd s u → Fupd t z → P u z) :
    RelCT isa (WithFlag P bit) (.block [.alu .cmp .eax (.imm 0)])
      (fun s t => WithCondition P .e (!bit) s t ∧ WithCondition P .ne bit s t) := by
  intro s t tr ur u z ⟨H, flagS, flagT⟩ A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block [.alu .cmp .eax (.imm 0)])
      (VG.X86.Taint.Agree (τr [])) := checkedBlockInvariant rfl rfl
  have empty : VG.X86.Taint.Agree (τr []) s t := agree_regs (by intro r mem; cases mem)
  obtain ⟨U, eqU, neU⟩ := wp_result (cmp_bool flagS) A
  obtain ⟨Z, eqZ, neZ⟩ := wp_result (cmp_bool flagT) B
  exact ⟨(raw _ _ _ _ _ _ empty A B).1, ⟨keep _ _ _ _ H U Z, eqU, eqZ⟩, ⟨keep _ _ _ _ H U Z, neU, neZ⟩⟩

theorem branch_true {P Q : State → State → Prop} {c : Cond} {th el : Prog isa}
    (H : RelCT isa P th Q) :
    RelCT isa (WithCondition P c true) (.ite c th el) Q := by
  apply VG.RelCT.ite (fun _ _ P => P.2.1.trans P.2.2.symm)
  · exact H.mono (fun _ _ P => P.1.1) (fun _ _ P => P)
  · intro s t tr ur u z P _ _
    have impossible := P.1.2.1.symm.trans P.2
    cases impossible

theorem branch_false {P Q : State → State → Prop} {c : Cond} {th el : Prog isa}
    (H : RelCT isa P el Q) :
    RelCT isa (WithCondition P c false) (.ite c th el) Q := by
  apply VG.RelCT.ite (fun _ _ P => P.2.1.trans P.2.2.symm)
  · intro s t tr ur u z P _ _
    have impossible := P.1.2.1.symm.trans P.2
    cases impossible
  · exact H.mono (fun _ _ P => P.1.1) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.Candidate
