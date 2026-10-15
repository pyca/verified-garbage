module

public import VerifiedGarbage.Impl.Dsa.X86.Shape
public import VerifiedGarbage.Impl.Dsa.X86.Minus

/-! # DSA domain, key, and scalar validation

After public shape validation, every check accumulates a mask. Secret
scalar ranges and private/public key consistency do not skip arithmetic.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Validate
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout

def accumulate : List Instr := andFlag (Layout.field .mask)

def lowerTwo (n : Nat) : List Instr :=
  lessThanConstant n (slot n 5) (slot n 7) 2 ++
    ([.alu .xor .eax (.imm (BitVec.allOnes 32)), .mov .edx (.reg .eax)] : List Instr) ++ accumulate

def range (len : Nat) (modulus : Field) (input : Pointer) (aboveOne : Bool := false) : List Instr :=
  let n := (len + 7) / 8
  Core.load n len (slot n 0) (.input modulus) ++ Core.load n len (slot n 5) input ++
    checkRange n (slot n 5) (slot n 0) (Layout.field .mask) ++
    (if aboveOne then lowerTwo n else [])

def equalValues (len : Nat) (a b : Pointer) : List Instr :=
  let n := (len + 7) / 8
  Core.load n len (slot n 5) a ++ Core.load n len (slot n 8) b ++
    equal n (slot n 5) (slot n 8) ++ accumulate

def isOne (len : Nat) (input : Pointer) : List Instr :=
  let n := (len + 7) / 8
  Core.load n len (slot n 5) input ++ VG.Impl.Weierstrass.X86.setConst n (slot n 8) 1 ++
    equal n (slot n 5) (slot n 8) ++ accumulate

def zero (len : Nat) (input : Pointer) (wantNonzero : Bool := false) : List Instr :=
  let n := (len + 7) / 8
  Core.load n len (slot n 5) input ++ checkZero n (slot n 5) (Layout.field .mask) wantNonzero

def minus (len : Nat) (modulus : Field) (amount output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.setup len modulus)
    (.block (modulusMinus n amount ++ Core.store n len output))

def domain (pLen qLen : Nat) : Prog isa := Core.sequence [
  .block (range pLen .p (.input .g) true ++ range pLen .p (.input .y) true),
  minus pLen .p 1 t,
  Core.reduce qLen pLen (.local t) u,
  .block (zero qLen (.local u)),
  minus qLen .q 2 qMinusTwo]

def subgroup (pLen qLen : Nat) : Prog isa := Core.sequence [
  Core.power pLen qLen .p (.input .g) (.input .q) t,
  .block (isOne pLen (.local t)),
  Core.power pLen qLen .p (.input .y) (.input .q) t,
  .block (isOne pLen (.local t))]

def publicKey (pLen qLen : Nat) : Prog isa :=
  .seq (domain pLen qLen) (subgroup pLen qLen)

def privateKey (pLen qLen : Nat) : Prog isa := Core.sequence [
  .block (range qLen .q (.input .x) ++ range qLen .q (.input .nonce)),
  Core.power pLen qLen .p (.input .g) (.input .x) t,
  .block (equalValues pLen (.local t) (.input .y))]

end VG.Impl.Dsa.X86.Validate
