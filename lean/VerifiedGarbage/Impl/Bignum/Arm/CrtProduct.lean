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
/-- The counts of a product of the factors at their own widths: `⌈p_len / 4⌉`
rows, of `⌈q_len / 4⌉` words each, from the private CRT frame's lengths of
`p` and `q` (slots 68 and 76), for factors of those lengths. -/
def lengthCount : List Instr :=
  [.ldrSp .r1 68, .dp .add .r1 .r1 (.imm 3), .mov .r1 (.shifted .r1 .lsr 2), .str .r1 .r0 140,
   .ldrSp .r1 76, .dp .add .r1 .r1 (.imm 3), .mov .r1 (.shifted .r1 .lsr 2), .str .r1 .r0 144]
def productOperandSlot (coefficient : Bool) : Nat := if coefficient then 104 else 64
/-- The product's operands and output, and its counts by `count`. -/
def productArgsWith (coefficient : Bool) (count : List Instr) : Prog isa :=
  .seq (.block (copyChildPointer 224 128 (productOperandSlot coefficient))) (.seq (.block (copyChildPointer 228 132))
    (.seq (.block (copyHeaderPointer 232 136)) (.block count)))
def productArgs (coefficient : Bool := false) : Prog isa := productArgsWith coefficient productCount
/-- The product, its output cleared first, with the counts `count` sets. -/
def factorProductWith (coefficient : Bool) (count : List Instr) : Prog isa :=
  .seq (clearWide 232) (.seq (productArgsWith coefficient count) wideProduct)
def factorProduct (coefficient : Bool := false) : Prog isa := factorProductWith coefficient productCount

end VG.Impl.Bignum.Arm.Crt
