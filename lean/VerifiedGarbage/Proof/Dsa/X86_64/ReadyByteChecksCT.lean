module
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT

/-! # Byte validation timing from the persistent public field bindings -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem readyZero_ct {a : Operand} (ha : pointerFits a.pointer)
    (hp : stablePointer a.pointer) (hl : a.length ≠ .mask) (nonzero : Bool)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Core.pointer a.pointer ++
      ([.mov .rsi (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) hc).isSome = true) :
    RelCT isa (Two Ready) (Checks.zero a nonzero) (fun _ _ => True) := by
  refine two_map (fun L : ExecutionLayout =>
    (⟨L.base, L.pointer a.pointer, (L.fields a.length).toNat⟩ : ZeroPublic)) ?_ (zero_ct ha nonzero hT)
  intro L s h
  refine ⟨activeBytes, h.parent.scr, by decide, h.parent.rdi, h.publicPointer a.pointer hp, ?_⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields a.length hl

theorem readyEqual_ct {a b : Operand} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer) (hl : a.length ≠ .mask) (unequal : Bool)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Core.pointer a.pointer ++
      ([.mov .rsi (.reg .rax)] : List Instr) ++ Core.pointer b.pointer ++
      ([.mov .rdx (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) hc).isSome = true) :
    RelCT isa (Two Ready) (Checks.equal a b unequal) (fun _ _ => True) := by
  refine two_map (fun L : ExecutionLayout =>
    (⟨L.base, L.pointer a.pointer, L.pointer b.pointer, (L.fields a.length).toNat⟩ : EqualPublic)) ?_
    (equal_ct ha hb unequal hT)
  intro L s h
  refine ⟨activeBytes, h.parent.scr, by decide, h.parent.rdi,
    h.publicPointer a.pointer hpa, h.publicPointer b.pointer hpb, ?_⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields a.length hl

end VG.Proof.Dsa.X86_64
