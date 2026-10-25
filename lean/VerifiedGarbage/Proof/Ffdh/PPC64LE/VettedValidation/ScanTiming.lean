module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.RecordTiming
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Record

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
      refine WP.mono_syms (withSp (record_ok h.1 g h.2.1 h.2.2.1.1 (by rw [total] at fit; omega))) ?_
      rintro t ⟨⟨zero, mem, rest⟩, sp⟩ sym
      exact ⟨⟨h.1.after mem rest, sym ▸ h.2.1, h.2.2.1.after mem rest, sp.trans h.2.2.2⟩, zero⟩
    have stepCT := (record_ct (src := src) (table := table) (stack := stack) (k := k) (dom := dom)
      g (valid g (by simp)) (offset := offset) (by rw [total] at fit; omega)).mono
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
          omega
        exact (ih (offset + 8 + 3 * g.len) (by rw [total] at fit; omega)
          (fun x hx => valid x (by simp [hx]))).mono
          (fun s t h => ⟨⟨h.1.1.1.1, h.1.1.1.2.1, by rw [← ptr]; exact h.1.1.1.2.2.1.2, h.1.1.1.2.2.2⟩,
            ⟨h.1.2.1.1, h.1.2.1.2.1, by rw [← ptr]; exact h.1.2.1.2.2.1.2, h.1.2.1.2.2.2⟩⟩)
          (fun _ _ h => h)
    rw [scan]
    exact ((stepCT.wp (fun s t h => ⟨stepWP s h.1, stepWP t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq branches

end VG.Proof.Ffdh.PPC64LE.VettedValidation
