module

import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Impl.Ffdh.X86.VettedValidation
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Record
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.State

/-! ### `Ffdh.X86.VettedValidation.RecordTiming`, which only this module used -/

section

/-! Each record's trace uses only public widths, pointers, and the fixed comparison loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem record_ct {base src sp table : BitVec 32} {k offset : Nat} {dom : List Byte}
    (g : Group) (lenFit : g.len < 2 ^ 32)  :
    RelCT isa (fun s t =>
      Context base src sp table k dom s ∧
      Context base src sp table k dom t)
      (record g offset) (fun _ _ => True) := by
  let P := fun s : State => Context base src sp table k dom s
  let H := fun s : State => P s ∧ s.zf = some (decide (g.len = k))
  let A := fun s : State => Context base src sp table k dom s ∧
    s.gpr .esi = src ∧ s.gpr .edi = table + BitVec.ofNat 32 (offset + 8) ∧
    s.gpr .ecx = BitVec.ofNat 32 dom.length
  have headerCT : RelCT isa (fun s t => P s ∧ P t) (.block (header g)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp]) _ (hc := .block []) (by rfl)
    intro s t h
    apply agree_regs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.stack.trans h.2.stack.symm
  have headerWP (s : State) (h : P s) : WP isa (.block (header g)) s H := by
    refine WP.mono_syms (header_ok h g lenFit) ?_
    rintro t ⟨zero, mem, rest⟩ _sym
    exact ⟨h.after mem rest, zero⟩
  have argsCT : RelCT isa (fun s t => P s ∧ P t) (.block (compareArgs offset)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp, .ebx]) _ (hc := .block []) (by rfl)
    intro s t h
    apply agree_regs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.stack.trans h.2.stack.symm
    · exact h.1.baseReg.trans h.2.baseReg.symm
  have argsWP (s : State) (h : P s) : WP isa (.block (compareArgs offset)) s A := by
    refine WP.mono (args_ok h) ?_
    rintro t ⟨src, ptr, length, mem, rest⟩
    exact ⟨h.after mem rest, src, ptr, length⟩
  have compareCT : RelCT isa (fun s t => A s ∧ A t)
      VG.Impl.RsaPkcs1Sig.X86.compare (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esi, .edi, .ecx]) _ (by taint_decide)
    intro s t h
    apply agree_regs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  have compareStage := ((argsCT.wp (fun s t h => ⟨argsWP s h.1, argsWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq compareCT
  have choice : RelCT isa (fun s t => H s ∧ H t)
      (.ite .e (.seq (.block (compareArgs offset)) VG.Impl.RsaPkcs1Sig.X86.compare) (.block [.mov .ebp (.imm 1)]))
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by simp only [eval, h.1.2, h.2.2])
    · exact compareStage.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
    · apply RelCT.taint (A := taint) (τr []) _ (hc := .block []) (by rfl)
      intro _ _ _
      exact agree_regs (by simp)
  have testCT : RelCT isa (fun _ _ => True) (.block [.alu .test .ebp (.reg .ebp)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) _ (by taint_decide)
    intro _ _ _
    exact agree_regs (by simp)
  unfold record
  exact ((headerCT.wp (fun s t h => ⟨headerWP s h.1, headerWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq (choice.seq testCT)

end VG.Proof.Ffdh.X86.VettedValidation

end

end

/-! The scan branches only on exact matches against the already-public input. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem scan_ct {base src sp table : BitVec 32} {k : Nat} {dom : List Byte}
    (gs : List Group) (offset : Nat)
    (fit : offset + (gs.flatMap Group.bytes).length ≤ 17744)
    (valid : ∀ g ∈ gs, g.len < 2 ^ 32) :
    RelCT isa (fun s t =>
      (Context base src sp table k dom s ∧
        TableAt (byteAddr table + BitVec.ofNat 64 offset) gs s) ∧
      (Context base src sp table k dom t ∧
        TableAt (byteAddr table + BitVec.ofNat 64 offset) gs t))
      (scan gs offset) (fun _ _ => True) := by
  induction gs generalizing offset with
  | nil =>
    apply RelCT.taint (A := taint) (τr []) _ (hc := .block []) (by rfl)
    intro _ _ _
    exact agree_regs (by simp)
  | cons g gs ih =>
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, VG.Proof.Ffdh.VettedTableFacts.groupBytes_length]
    let P := fun s : State => Context base src sp table k dom s ∧
      TableAt (byteAddr table + BitVec.ofNat 64 offset) (g :: gs) s
    let H := fun s : State => P s ∧
      s.zf = some (decide (g.len = k ∧ dom = g.domain.take dom.length))
    have stepWP (s : State) (h : P s) : WP isa (record g offset) s H := by
      refine WP.mono (record_ok h.1 g h.2.1 (by rw [total] at fit; omega_using [fit])) ?_
      rintro t ⟨zero, mem, rest⟩
      exact ⟨⟨h.1.after mem rest, h.2.after mem rest⟩, zero⟩
    have stepCT := (record_ct (base := base) (src := src) (sp := sp) (table := table) (k := k) (dom := dom)
      g (valid g (by simp)) (offset := offset)).mono
      (P' := fun s t => P s ∧ P t)
      (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
    have branches : RelCT isa (fun s t => H s ∧ H t)
        (.ite .e (.block [.mov .eax (.imm (BitVec.ofNat 32 g.bits))])
          (scan gs (offset + 8 + 3 * g.len))) (fun _ _ => True) := by
      apply RelCT.ite (fun s t h => by simp only [eval, h.1.2, h.2.2])
      · apply RelCT.taint (A := taint) (τr []) _ (hc := .block []) (by rfl)
        intro _ _ _
        exact agree_regs (by simp)
      · have ptr : (byteAddr table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 (8 + 3 * g.len) =
            byteAddr table + BitVec.ofNat 64 (offset + 8 + 3 * g.len) := by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
          congr 2
          omega_using []
        exact (ih (offset + 8 + 3 * g.len) (by rw [total] at fit; omega_using [fit])
          (fun x hx => valid x (by simp [hx]))).mono
          (fun s t h => ⟨⟨h.1.1.1.1, by rw [← ptr]; exact h.1.1.1.2.2⟩,
            ⟨h.1.2.1.1, by rw [← ptr]; exact h.1.2.1.2.2⟩⟩)
          (fun _ _ h => h)
    rw [scan]
    exact ((stepCT.wp (fun s t h => ⟨stepWP s h.1, stepWP t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq branches

end VG.Proof.Ffdh.X86.VettedValidation
