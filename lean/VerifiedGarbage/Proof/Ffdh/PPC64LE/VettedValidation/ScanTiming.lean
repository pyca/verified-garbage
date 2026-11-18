module

import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Record
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym

/-! ### `Ffdh.PPC64LE.VettedValidation.RecordTiming`, which this module and modules that import it used -/

section

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

end

end

/-! The scan branches only on exact matches against the already-public input. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem scan_ct {src table stack : Addr} {k : Nat} {dom : List Byte}
    (gs : List Group) (offset : Nat)
    (fit : offset + (gs.flatMap Group.bytes).length ≤ 17744)
    (valid : ∀ g ∈ gs, g.len < 2 ^ 15) :
    RelCT isa (fun s t =>
      (Context src k dom s ∧ s.syms tableSym = table ∧
        TableAt (table + BitVec.ofNat 64 offset) gs s ∧ s.sp = stack) ∧
      (Context src k dom t ∧ t.syms tableSym = table ∧
        TableAt (table + BitVec.ofNat 64 offset) gs t ∧ t.sp = stack))
      (scan gs offset) (fun _ _ => True) := by
  induction gs generalizing offset with
  | nil =>
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t h
    exact ⟨h.1.2.2.2.trans h.2.2.2.2.symm, by simp [Taint.ofRegs]⟩
  | cons g gs ih =>
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, VG.Proof.Ffdh.VettedTableFacts.groupBytes_length]
    let P := fun s : State => Context src k dom s ∧ s.syms tableSym = table ∧
      TableAt (table + BitVec.ofNat 64 offset) (g :: gs) s ∧ s.sp = stack
    let H := fun s : State => P s ∧
      (s.gpr .r10 = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length)
    have stepWP (s : State) (h : P s) : WP isa (record g offset) s H := by
      refine WP.mono_syms (withSp (record_ok h.1 g h.2.1 h.2.2.1.1 (by rw [total] at fit; omega_using [fit]))) ?_
      rintro t ⟨⟨zero, mem, rest⟩, sp⟩ sym
      exact ⟨⟨h.1.after mem rest, sym ▸ h.2.1, h.2.2.1.after mem rest, sp.trans h.2.2.2⟩, zero⟩
    have stepCT := (record_ct (src := src) (table := table) (stack := stack) (k := k) (dom := dom)
      g (valid g (by simp)) (offset := offset) (by rw [total] at fit; omega_using [fit])).mono
      (P' := fun s t => P s ∧ P t)
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2.2⟩⟩) (fun _ _ h => h)
    have branches : RelCT isa (fun s t => H s ∧ H t)
        (.ite (.zero .d .r10) (.block [.li .r8 g.bits])
          (scan gs (offset + 8 + 3 * g.len))) (fun _ _ => True) := by
      apply RelCT.ite (fun s t h => by
        rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero, VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero]
        congr 1
        apply Bool.eq_iff_iff.mpr
        simpa only [beq_iff_eq] using h.1.2.trans h.2.2.symm)
      · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
        intro s t h
        exact ⟨h.1.1.1.2.2.2.trans h.1.2.1.2.2.2.symm, by simp [Taint.ofRegs]⟩
      · have ptr : (table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 (8 + 3 * g.len) =
            table + BitVec.ofNat 64 (offset + 8 + 3 * g.len) := by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
          congr 2
          omega_using []
        exact (ih (offset + 8 + 3 * g.len) (by rw [total] at fit; omega_using [fit])
          (fun x hx => valid x (by simp [hx]))).mono
          (fun s t h => ⟨⟨h.1.1.1.1, h.1.1.1.2.1, by rw [← ptr]; exact h.1.1.1.2.2.1.2, h.1.1.1.2.2.2⟩,
            ⟨h.1.2.1.1, h.1.2.1.2.1, by rw [← ptr]; exact h.1.2.1.2.2.1.2, h.1.2.1.2.2.2⟩⟩)
          (fun _ _ h => h)
    rw [scan]
    exact ((stepCT.wp (fun s t h => ⟨stepWP s h.1, stepWP t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq branches

end VG.Proof.Ffdh.PPC64LE.VettedValidation
