module

public import VerifiedGarbage.Impl.Dsa.X86.Minus
public import VerifiedGarbage.Impl.Dsa.X86.Core
public import VerifiedGarbage.Impl.Dsa.X86.Width

/-! # DSA domain, key, and scalar validation

After public shape validation, every check accumulates a mask. Secret
scalar ranges and private/public key consistency do not skip arithmetic.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Validate
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout

def accumulate : List Instr := andFlag (Layout.field .mask)

def lowerTwo (n : Nat) : Prog isa :=
  .seq (lessThanConstant n (slot n 5) (slot n 7) 2)
    (.block ([.alu .xor .eax (.imm (BitVec.allOnes 32)), .mov .edx (.reg .eax)] ++ accumulate))

def range (len : Nat) (modulus : Field) (input : Pointer) (aboveOne : Bool := false) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (slot n 0) (.input modulus)) (.seq (Core.load n len (slot n 5) input)
    (.seq (checkRange n (slot n 5) (slot n 0) (Layout.field .mask))
    (if aboveOne then lowerTwo n else .block [])))

def equalValues (len : Nat) (a b : Pointer) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (slot n 5) a) (.seq (Core.load n len (slot n 8) b)
    (.seq (equal n (slot n 5) (slot n 8)) (.block accumulate)))

def isOne (len : Nat) (input : Pointer) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (slot n 5) input) (.seq (setConstW (2 * n) (slot n 8) 1)
    (.seq (equal n (slot n 5) (slot n 8)) (.block accumulate)))

def zero (len : Nat) (input : Pointer) (wantNonzero : Bool := false) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (slot n 5) input) (checkZero n (slot n 5) (Layout.field .mask) wantNonzero)

def minus (len : Nat) (modulus : Field) (amount output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.setup len modulus) (.seq (modulusMinus n amount) (Core.store len output))

def domain (pLen qLen : Nat) : Prog isa := Core.sequence [
  .seq (range pLen .p (.input .g) true) (range pLen .p (.input .y) true),
  minus pLen .p 1 t,
  Core.reduce qLen (.imm (BitVec.ofNat 32 pLen)) (.local t) u,
  zero qLen (.local u),
  minus qLen .q 2 qMinusTwo]

def subgroup (pLen qLen : Nat) : Prog isa := Core.sequence [
  Core.power pLen qLen .p (.input .g) (.input .q) t,
  isOne pLen (.local t),
  Core.power pLen qLen .p (.input .y) (.input .q) t,
  isOne pLen (.local t)]

def publicKey (pLen qLen : Nat) : Prog isa :=
  .seq (domain pLen qLen) (subgroup pLen qLen)

def privateKey (pLen qLen : Nat) : Prog isa := Core.sequence [
  .seq (range qLen .q (.input .x)) (range qLen .q (.input .nonce)),
  Core.power pLen qLen .p (.input .g) (.input .x) t,
  equalValues pLen (.local t) (.input .y)]

end VG.Impl.Dsa.X86.Validate
