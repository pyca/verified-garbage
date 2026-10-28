module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentInitial
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Native candidate timing shares public pointers and exponent bytes across secret inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure InputPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop where
  left : Input E eBytes pBytes rBytes s
  right : Input E eBytes qBytes sBytes t

structure DrawnPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop where
  left : Drawn E eBytes pBytes rBytes s
  right : Drawn E eBytes qBytes sBytes t

theorem InputPair.agree {E : Environment} {eBytes pBytes qBytes rBytes sBytes : List Byte} {s t : State}
    (P : InputPair E eBytes pBytes qBytes rBytes sBytes s t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact P.left.stack.trans P.right.stack.symm
  · exact BitVec.eq_of_toNat_eq (P.left.scratch.edi_toNat.trans P.right.scratch.edi_toNat.symm)

theorem DrawnPair.inputs {E : Environment} {eBytes pBytes qBytes rBytes sBytes : List Byte} {s t : State}
    (P : DrawnPair E eBytes pBytes qBytes rBytes sBytes s t) : InputPair E eBytes pBytes qBytes rBytes sBytes s t :=
  ⟨P.left.input, P.right.input⟩

theorem Drawn.exponentInitial {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    CandidateExponent.Initial E.workspace E.p E.exponent E.size E.width (candidateValue E entropy)
      E.exponentLength (Spec.Rsa.os2ip eBytes) s := by
  refine ⟨D.input.scratch, D.input.stack, v.width_bounds.1, v.width_bounds.2, v.slotFit (by decide), D.candidate,
    by have := candidate_large v entropy; omega, candidate_odd v entropy, D.input.exponent_eq,
    D.input.exponentLength_eq v, by have := v.exponentLength.1; omega, v.exponentLength.2, v.exponentFit,
    D.input.memory.exponentRead, v.readWorkspace List.mem_cons_self, ?_, by have := v.low; omega, ?_, ?_⟩
  · rw [D.input.memory.exponentBytes]
  · change E.p.toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 40 ≤ E.p.toNat
    rcases v.workspaceStack with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · change s.mem.readW (off E.base (4 * 1)) 32 = _
    rw [D.input.header 1 (by decide), v.length_eq]; rfl

end VG.Proof.RsaKeyGen.X86.Candidate
