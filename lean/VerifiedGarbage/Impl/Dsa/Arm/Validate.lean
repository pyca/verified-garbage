module
public import VerifiedGarbage.Impl.Dsa.Arm.Core


/-! # DSA domain, key, and scalar validation on 32-bit ARM

After public shape validation, every check accumulates a mask. Secret
scalar ranges and private/public key consistency do not skip arithmetic.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Validate
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Impl.Dsa.Layout

def accumulate : List Instr := andFlag (Layout.field .mask)

def lowerTwo (n : Nat) : Prog isa :=
  .seq (lessThanConstant (2 * n) (baseS n) (prodS n) 2)
    (.block (allOnes ++ [.dp .eor .r2 .r2 (.reg .r4)] ++ accumulate))

def range (len : Nat) (modulus : Field) (input : Pointer) (aboveOne : Bool := false) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (modS n) (.input modulus)) (.seq (Core.load n len (baseS n) input)
    (.seq (checkRange (2 * n) (baseS n) (modS n) (Layout.field .mask))
    (if aboveOne then lowerTwo n else .block [])))

def equalValues (len : Nat) (a b : Pointer) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (baseS n) a) (.seq (Core.load n len (expS n) b)
    (.seq (equal (2 * n) (baseS n) (expS n)) (.block accumulate)))

def isOne (len : Nat) (input : Pointer) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (baseS n) input) (.seq (setConst (2 * n) (expS n) 1)
    (.seq (equal (2 * n) (baseS n) (expS n)) (.block accumulate)))

def zero (len : Nat) (input : Pointer) (wantNonzero : Bool := false) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (baseS n) input) (checkZero (2 * n) (baseS n) (Layout.field .mask) wantNonzero)

def minus (len : Nat) (modulus : Field) (amount output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.setup len modulus) (.seq (modulusMinus n amount) (Core.store len output))

def domain (pLen qLen : Nat) : Prog isa := Core.sequence [
  .seq (range pLen .p (.input .g) true) (range pLen .p (.input .y) true),
  minus pLen .p 1 t,
  Core.reduce qLen (.imm pLen) (.local t) u,
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

end VG.Impl.Dsa.Arm.Validate
