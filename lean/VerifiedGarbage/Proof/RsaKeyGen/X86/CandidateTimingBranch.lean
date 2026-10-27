module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatch
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words

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

theorem width_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : WP isa (.block VG.Impl.RsaKeyGen.X86.Candidate.width) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 E.width ∧ t.mem = s.mem ∧ Keeps [.eax] s t ∧ t.syms = s.syms := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  unfold VG.Impl.RsaKeyGen.X86.Candidate.width
  refine wp_movS (readSrc_sc I.scratch (d := 4) (by omega)) fun a A _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun t T => WP.block_nil ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.trans T.keeps, T.syms.trans A.syms⟩
  rw [T.gpr, A.gpr, I.header 1 (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  change (E.length % 2 ^ 32) / 8 = E.width % 2 ^ 32
  rw [Nat.mod_eq_of_lt (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega),
    Nat.mod_eq_of_lt (by have := v.width_bounds.2; omega)]
  rfl

/-- The width read from the header, by runs related by `P` whose inputs are
the candidate's. -/
theorem width_trace {E : Environment} (v : E.Valid) {P : State → State → Prop}
    {e₁ p₁ r₁ e₂ p₂ r₂ : List Byte}
    (left : ∀ s t, P s t → Input E e₁ p₁ r₁ s) (right : ∀ s t, P s t → Input E e₂ p₂ r₂ t)
    (keep : ∀ s t u z, P s t → u.mem = s.mem → z.mem = t.mem → Keeps [.eax] s u → Keeps [.eax] t z →
      u.syms = s.syms → z.syms = t.syms → P u z) :
    RelCT isa P (.block VG.Impl.RsaKeyGen.X86.Candidate.width) (WithValue P (BitVec.ofNat 32 E.width)) := by
  intro s t tr ur u z H A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block VG.Impl.RsaKeyGen.X86.Candidate.width)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  obtain ⟨valueU, memU, KU, symU⟩ := wp_result (width_ok v (left s t H)) A
  obtain ⟨valueZ, memZ, KZ, symZ⟩ := wp_result (width_ok v (right s t H)) B
  have agree : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
    have L := left s t H
    have R := right s t H
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact L.stack.trans R.stack.symm
    · exact BitVec.eq_of_toNat_eq (L.scratch.edi_toNat.trans R.scratch.edi_toNat.symm)
  exact ⟨(raw _ _ _ _ _ _ agree A B).1,
    keep _ _ _ _ H memU memZ KU KZ symU symZ, valueU, valueZ⟩

theorem dispatch_trace {part : Nat → Prog isa} {P Q : State → State → Prop} {w : Nat} (wBound : w < 2 ^ 32)
    (keep : ∀ s t u z, P s t → Fupd s u → Fupd t z → P u z) (H : RelCT isa P (part w) Q) :
    ∀ (widths : List Nat), w ∈ widths → (∀ x ∈ widths, x < 2 ^ 32) →
      RelCT isa (WithValue P (BitVec.ofNat 32 w)) (VG.Impl.RsaKeyGen.X86.Candidate.dispatch part widths) Q
  | [], member, _ => nomatch member
  | x :: rest, member, bounded => by
    unfold VG.Impl.RsaKeyGen.X86.Candidate.dispatch
    have compare := compare_value_trace (P := P) (BitVec.ofNat 32 w) (BitVec.ofNat 32 x) keep
    rw [width_comparison wBound (bounded x List.mem_cons_self)] at compare
    by_cases same : w = x
    · rw [decide_eq_true same] at compare
      refine RelCT.seq compare (branch_true ?_)
      rw [← same]
      exact H.mono (fun _ _ H => H.1) (fun _ _ q => q)
    · rw [decide_eq_false same] at compare
      exact RelCT.seq compare (branch_false (dispatch_trace wBound keep H rest
        (List.mem_cons.mp member |>.resolve_left same) (fun j mem => bounded j (List.mem_cons_of_mem _ mem))))

end VG.Proof.RsaKeyGen.X86.Candidate
