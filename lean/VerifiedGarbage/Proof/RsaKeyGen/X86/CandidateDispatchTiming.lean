module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatch
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.TCB.X86.Isa

/-! # Branches on public values and the width dispatch leak only the branch taken -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def WithFlag (P : State → State → Prop) (bit : Bool) (s t : State) : Prop :=
  P s t ∧ s.gpr .eax = BitVec.ofNat 32 bit.toNat ∧ t.gpr .eax = BitVec.ofNat 32 bit.toNat

def WithCondition (P : State → State → Prop) (c : Cond) (bit : Bool) (s t : State) : Prop :=
  P s t ∧ isa.eval c s = some bit ∧ isa.eval c t = some bit

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

def WithValue (P : State → State → Prop) (value : BitVec 32) (s t : State) : Prop :=
  P s t ∧ s.gpr .eax = value ∧ t.gpr .eax = value

theorem compare_value_ok {s : State} (value : BitVec 32) :
    WP isa (.block [.alu .cmp .eax (.imm value)]) s fun t =>
      Fupd s t ∧ isa.eval .e t = some (s.gpr .eax - value == 0#32) := by
  refine wp_cmpS rfl fun _ T Z => WP.block_nil ⟨T, ?_⟩
  exact Z

theorem compare_value_trace {P : State → State → Prop} (value immediate : BitVec 32)
    (keep : ∀ s t u z, P s t → Fupd s u → Fupd t z → P u z) :
    RelCT isa (WithValue P value) (.block [.alu .cmp .eax (.imm immediate)])
      (WithCondition (WithValue P value) .e (value - immediate == 0#32)) := by
  intro s t tr ur u z ⟨H, valueS, valueT⟩ A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block [.alu .cmp .eax (.imm immediate)])
      (VG.X86.Taint.Agree (τr [])) :=
    erased_relCT _ (.block [.alu .cmp .eax (.imm 0)]) (.block []) rfl rfl rfl (by decide +kernel)
  have empty : VG.X86.Taint.Agree (τr []) s t := agree_regs (by intro r mem; cases mem)
  obtain ⟨U, flagU⟩ := wp_result (compare_value_ok immediate) A
  obtain ⟨Z, flagZ⟩ := wp_result (compare_value_ok immediate) B
  refine ⟨(raw _ _ _ _ _ _ empty A B).1, ⟨keep _ _ _ _ H U Z, ?_, ?_⟩, ?_, ?_⟩
  · rw [U.gpr]; exact valueS
  · rw [Z.gpr]; exact valueT
  · rw [flagU, valueS]
  · rw [flagZ, valueT]

end VG.Proof.RsaKeyGen.X86.Candidate
