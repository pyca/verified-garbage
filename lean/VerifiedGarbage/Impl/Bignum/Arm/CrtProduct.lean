module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtClearWide
public import VerifiedGarbage.Impl.Bignum.Arm.WideProduct

/-! # Compute the full factor product for CRT key validation

The extended output is disjoint from both factor workspaces. The
schoolbook multiplication consumes every native word of both factors.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def copyChildPointer (src dst : Nat) (slot : Nat := 64) : List Instr :=
  [.ldr .r1 .r0 src, .ldr .r1 .r1 slot, .str .r1 .r0 dst]
def copyHeaderPointer (src dst : Nat) : List Instr := [.ldr .r1 .r0 src, .str .r1 .r0 dst]
def productCount : List Instr :=
  [.ldr .r1 .r0 48, .dp .add .r1 .r1 (.reg .r1), .str .r1 .r0 140, .str .r1 .r0 144]
def productOperandSlot (coefficient : Bool) : Nat := if coefficient then 104 else 64
def productArgs (coefficient : Bool := false) : Prog isa :=
  .seq (.block (copyChildPointer 224 128 (productOperandSlot coefficient))) (.seq (.block (copyChildPointer 228 132))
    (.seq (.block (copyHeaderPointer 232 136)) (.block productCount)))
def factorProduct (coefficient : Bool := false) : Prog isa := .seq (clearWide 232) (.seq (productArgs coefficient) wideProduct)

end VG.Impl.Bignum.Arm.Crt
