module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSizedTiming
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86.Isa

/-! # Public width comparisons retain the candidate's input relation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def WithValue (P : State → State → Prop) (value : BitVec 32) (s t : State) : Prop :=
  P s t ∧ s.gpr .eax = value ∧ t.gpr .eax = value

theorem ClearedPair.keepMem {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : ClearedPair E eBytes pBytes qBytes rBytes sBytes s t)
    (MU : u.mem = s.mem) (MZ : z.mem = t.mem) {regs : List Reg} (KU : Keeps regs s u) (KZ : Keeps regs t z)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (SU : u.syms = s.syms) (SZ : z.syms = t.syms) :
    ClearedPair E eBytes pBytes qBytes rBytes sBytes u z := by
  refine ⟨⟨P.left.keepMem v MU KU base sp SU, P.right.keepMem v MZ KZ base sp SZ⟩, ?_, ?_⟩
  · rw [MU]; exact P.zerosLeft
  · rw [MZ]; exact P.zerosRight

theorem ClearedPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : ClearedPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    ClearedPair E eBytes pBytes qBytes rBytes sBytes u z :=
  P.keepMem v U.mem Z.mem (U.keeps []) (Z.keeps []) (by decide) (by decide) U.syms Z.syms

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

theorem width_comparison {a b : Nat} (aBound : a < 2 ^ 32) (bBound : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0#32) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt aBound, Nat.mod_eq_of_lt bBound]

end VG.Proof.RsaKeyGen.X86.Candidate
