module

import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Record
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Encode
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.State

/-! Each record's trace uses only public widths, pointers, and the fixed comparison loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem record_ct {base src table : Addr} {k offset : Nat} {dom : List Byte}
    (g : Group) (lenFit : g.len < 2 ^ 31) (offsetFit : offset + 8 < 2 ^ 31) :
    RelCT isa (fun s t =>
      (Context base src k dom s ∧ s.syms tableSym = table) ∧
      (Context base src k dom t ∧ t.syms tableSym = table))
      (record g offset) (fun _ _ => True) := by
  let P := fun s : State => Context base src k dom s ∧ s.syms tableSym = table
  let H := fun s : State => P s ∧ s.zf = some (decide (g.len = k))
  let A := fun s : State => Context base src k dom s ∧
    s.gpr .rsi = table + BitVec.ofNat 64 (offset + 8) ∧
    s.gpr .rcx = BitVec.ofNat 64 dom.length
  have headerCT : RelCT isa (fun s t => P s ∧ P t) (.block (header g)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r9]) _ (hc := .block []) (by rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.1.baseReg.trans h.2.1.baseReg.symm
  have headerWP (s : State) (h : P s) : WP isa (.block (header g)) s H := by
    refine WP.mono_syms (header_ok h.1 g lenFit) ?_
    rintro t ⟨zero, _, mem, rest⟩ sym
    exact ⟨⟨h.1.after mem rest, sym ▸ h.2⟩, zero⟩
  have argsCT : RelCT isa (fun s t => P s ∧ P t) (.block (compareArgs offset)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r9]) _ (hc := .block []) (by
      rw [← (taint_eraseInv.check (.block (compareArgs offset)) (Taint.ofRegs [.r9])
        (.block []) rfl).1]
      change (taint.check (Taint.ofRegs [.r9]) (.block [
        .leaSym .rsi tableSym, .alu .add .rsi (.imm 0),
        .mov .rcx (.mem (VG.Impl.MlKem.X86_64.at_ .r9 0))]) (.block [])).isSome = true
      decide +kernel)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.1.baseReg.trans h.2.1.baseReg.symm
  have argsWP (s : State) (h : P s) : WP isa (.block (compareArgs offset)) s A := by
    refine WP.mono (args_ok h.1 h.2 offsetFit) ?_
    rintro t ⟨ptr, length, mem, rest⟩
    exact ⟨h.1.after mem rest, ptr, length⟩
  have compareCT : RelCT isa (fun s t => A s ∧ A t)
      VG.Impl.RsaPkcs1Sig.X86_64.compare (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rcx]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.1.source.trans h.2.1.source.symm
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.trans h.2.2.2.symm
  have compareStage := ((argsCT.wp (fun s t h => ⟨argsWP s h.1, argsWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq compareCT
  have choice : RelCT isa (fun s t => H s ∧ H t)
      (.ite .e (.seq (.block (compareArgs offset)) VG.Impl.RsaPkcs1Sig.X86_64.compare) (.block []))
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by simp only [eval, h.1.2, h.2.2])
    · exact compareStage.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
    · exact RelCT.block_nil (fun _ _ _ => trivial)
  have testCT : RelCT isa (fun _ _ => True) (.block [.alu .test .rdx (.reg .rdx)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _
    exact Taint.agree_ofRegs (by simp)
  unfold record
  exact ((headerCT.wp (fun s t h => ⟨headerWP s h.1, headerWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq (choice.seq testCT)

end VG.Proof.Ffdh.X86_64.VettedValidation
