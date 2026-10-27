module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatchTiming
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

end VG.Proof.RsaKeyGen.X86.Candidate
