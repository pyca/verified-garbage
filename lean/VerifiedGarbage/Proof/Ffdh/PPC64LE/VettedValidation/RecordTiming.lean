module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Record
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation

/-! Fixed-length comparison leaks only the original public lengths and pointers. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem withSp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.sp = s.sp := by
  obtain ⟨tr, t, run, post⟩ := h
  exact ⟨tr, t, run, post, Exec.sp run⟩

theorem record_ct {src table stack : Addr} {k offset : Nat} {dom : List Byte}
    (g : Group) (lenFit : g.len < 2 ^ 15) (offsetFit : offset + 8 < 2 ^ 15) :
    RelCT isa (fun s t =>
      (Context src k dom s ∧ s.syms tableSym = table ∧ s.sp = stack) ∧
      (Context src k dom t ∧ t.syms tableSym = table ∧ t.sp = stack))
      (record g offset) (fun _ _ => True) := by
  let P := fun s : State => Context src k dom s ∧ s.syms tableSym = table ∧ s.sp = stack
  let H := fun s : State => P s ∧ (s.gpr .r0 = 0 ↔ g.len = k)
  let A := fun s : State => Context src k dom s ∧
    s.gpr .r8 = table + BitVec.ofNat 64 (offset + 8) ∧ s.sp = stack
  have headerCT : RelCT isa (fun s t => P s ∧ P t)
      (.block [.subi .r0 .r5 g.len]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t h
    exact ⟨h.1.2.2.trans h.2.2.2.symm, by simp [Taint.ofRegs]⟩
  have headerWP (s : State) (h : P s) : WP isa (.block [.subi .r0 .r5 g.len]) s H := by
    refine WP.mono_syms (withSp (header_ok h.1 g lenFit)) ?_
    rintro t ⟨⟨zero, mem, rest⟩, sp⟩ sym
    exact ⟨⟨h.1.after mem rest, sym ▸ h.2.1, sp.trans h.2.2⟩, zero⟩
  have argsCT : RelCT isa (fun s t => P s ∧ P t)
      (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taintSym [tableSym]) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t h
    refine ⟨⟨h.1.2.2.trans h.2.2.2.symm, by simp [Taint.ofRegs]⟩, ?_⟩
    intro name member
    obtain rfl := List.mem_singleton.mp member
    exact h.1.2.1.trans h.2.2.1.symm
  have argsWP (s : State) (h : P s) :
      WP isa (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)]) s A := by
    refine WP.mono (withSp (args_ok h.2.1 offsetFit)) ?_
    rintro t ⟨⟨ptr, mem, rest⟩, sp⟩
    exact ⟨h.1.after mem rest, ptr, sp.trans h.2.2⟩
  have compareCT : RelCT isa (fun s t => A s ∧ A t)
      VG.Impl.Ffdh.PPC64LE.VettedValidation.compare (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r8]) _ (by taint_decide)
    intro s t h
    refine ⟨h.1.2.2.trans h.2.2.2.symm, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.1.source.trans h.2.1.source.symm
    · exact h.1.1.length.trans h.2.1.length.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have compareStage := ((argsCT.wp (fun s t h => ⟨argsWP s h.1, argsWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq compareCT
  have choice : RelCT isa (fun s t => H s ∧ H t)
      (.ite (.zero .d .r0)
        (.seq (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)])
          VG.Impl.Ffdh.PPC64LE.VettedValidation.compare) (.block [.li .r10 1]))
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => ?_)
    · exact compareStage.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
    · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro s t h
      exact ⟨h.1.1.1.2.2.trans h.1.2.1.2.2.symm, by simp [Taint.ofRegs]⟩
    · rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero, VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq] using h.1.2.trans h.2.2.symm
  unfold record
  exact ((headerCT.wp (fun s t h => ⟨headerWP s h.1, headerWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq choice

end VG.Proof.Ffdh.PPC64LE.VettedValidation
