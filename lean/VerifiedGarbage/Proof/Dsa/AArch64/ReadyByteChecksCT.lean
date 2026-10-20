module
public import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands

import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
import VerifiedGarbage.Proof.Dsa.AArch64.EqualCT

/-! # Byte validation timing from the persistent public field bindings -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG.Impl.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem readyZero_ct {a : Operand} (ha : pointerFits a.pointer)
    (hp : stablePointer a.pointer) (hl : a.length ≠ .mask) (nonzero : Bool)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.pointer a.pointer ++
      ([mov .x1 .x3, Core.field .x9 a.length,
        movi .x8 0] : List Instr))) hc).isSome = true) :
    RelCT isa (Two Ready) (Checks.zero a nonzero) (fun _ _ => True) := by
  refine two_map (fun L : ExecutionLayout =>
    (⟨L.base, L.pointer a.pointer, (L.fields a.length).toNat⟩ : ZeroPublic)) ?_ (zero_ct ha nonzero hT)
  intro L s h
  refine ⟨activeBytes, h.parent.scr, by decide, h.parent.x0, h.publicPointer a.pointer hp, ?_⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields a.length hl

theorem readyEqual_ct {a b : Operand} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer) (hl : a.length ≠ .mask) (unequal : Bool)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.pointer a.pointer ++
      ([mov .x1 .x3] : List Instr) ++ Core.pointer b.pointer ++
      ([mov .x2 .x3, Core.field .x9 a.length,
        movi .x8 0] : List Instr))) hc).isSome = true) :
    RelCT isa (Two Ready) (Checks.equal a b unequal) (fun _ _ => True) := by
  refine two_map (fun L : ExecutionLayout =>
    (⟨L.base, L.pointer a.pointer, L.pointer b.pointer, (L.fields a.length).toNat⟩ : EqualPublic)) ?_
    (equal_ct ha hb unequal hT)
  intro L s h
  refine ⟨activeBytes, h.parent.scr, by decide, h.parent.x0,
    h.publicPointer a.pointer hpa, h.publicPointer b.pointer hpb, ?_⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields a.length hl

end VG.Proof.Dsa.AArch64
