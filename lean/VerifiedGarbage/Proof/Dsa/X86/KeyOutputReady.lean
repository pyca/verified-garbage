module

public import VerifiedGarbage.Proof.Dsa.X86.WriteKeyTiming
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
import VerifiedGarbage.Proof.Dsa.X86.KeyPartsReady
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # Output resources retained across domain checks and exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure KeyOutputReady (L : CallLayout) (out : BitVec 32) (s : State) : Prop where
  pointer : pointerValue L.base s (.input .out) = out
  write : ∀ i < 3 * L.pLen + 2 * L.qLen, InRegions s.wr (off (out.setWidth 64) i) 1
  params : Region.Disjoint ⟨(pointerValue L.base s (.input .p)).setWidth 64, 2 * L.pLen + L.qLen⟩
    ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩
  scalar : Region.Disjoint ⟨(pointerValue L.base s (.input .nonce)).setWidth 64, L.qLen⟩
    ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩

theorem KeyOutputReady.keep {L : CallLayout} {out : BitVec 32} {s t : State}
    (R : KeyOutputReady L out s) (E : Execution L.base s t) : KeyOutputReady L out t := by
  have ptr (f : Field) (stable : StablePointer (.input f)) := runFrame_pointer E.mem E.keeps (by decide) stable
  exact ⟨(ptr .out (by decide)).trans R.pointer, by rw [E.keeps.2.2]; exact R.write,
    by rw [ptr .p (by decide)]; exact R.params, by rw [ptr .nonce (by decide)]; exact R.scalar⟩

theorem KeyOutputReady.shape {L : CallLayout} {out : BitVec 32} {s t : State} {regs : List Reg}
    (R : KeyOutputReady L out s) (O : Outs L.base shapeRanges s.mem t.mem) (K : Keeps regs s t) :
    KeyOutputReady L out t := by
  exact ⟨(shapeFrame_field O (by decide)).trans R.pointer, by rw [K.2.2]; exact R.write,
    by rw [shapeFrame_field O (by decide : Field.p ≠ .mask ∧ Field.p ≠ .digestPrefixLen)]; exact R.params,
    by rw [shapeFrame_field O (by decide : Field.nonce ≠ .mask ∧ Field.nonce ≠ .digestPrefixLen)]; exact R.scalar⟩

theorem KeyOutputReady.writeReady {L : CallLayout} {out : BitVec 32} {s : State}
    (R : KeyOutputReady L out s) (C : CallReady L s)
    (P : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩) :
    KeyWriteReady L.base L.size L.pLen L.qLen out s := by
  have W := L.lengths
  refine ⟨C.moduli.scr, ?_, R.pointer, R.write⟩
  intro part member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (C.buffers _ P).keyPart (by omega) R.params
  · exact localKeyPart C.moduli.scr (by omega) (Nat.le_trans (C.moduli.wideFit (by decide)) L.extent) A
  · exact (C.buffers _ X).keyPart (by omega) R.scalar

end VG.Proof.Dsa.X86
