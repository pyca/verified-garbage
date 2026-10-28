module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key

/-! # Shared runtime-width arithmetic for RSA key generation

The cdecl length arguments select the modulus, prime and exponent widths.
Division and inversion share one set of word loops across all supported
widths, and so do the input and output.
The four-word correction bank is fixed.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

inductive Width | modulus | prime | exponent | correction
  deriving DecidableEq, Repr

def Width.words (n : Nat) : Width → Nat
  | .modulus => n
  | .prime => n / 2
  | .exponent => 2
  | .correction => 4

def Width.len (n : Nat) : Width → Nat
  | .modulus => 4 * n
  | .prime => 2 * n
  | .exponent => 8
  | .correction => 16

def Width.lay : Width → VG.Impl.Rsa.X86.KeyRt.Lay
  | .modulus => { len := 7, ws := 20 }
  | .prime => { len := 9, ws := 20 }
  | .exponent => { len := 19, ws := 20 }
  | .correction => { len := 7, ws := 20 }

def bytes (w : Width) (r : Reg) : List Instr :=
  match w with
  | .correction => [.mov r (.imm 16)]
  | _ => VG.Impl.Rsa.X86.KeyRt.bytesB w.lay r

inductive Loc | array (w : Width) (j : Nat) | fixed (offset : Nat)

def Loc.offset (n : Nat) : Loc → Nat
  | .array w j => slot (w.words n) j
  | .fixed offset => offset

def arr (j : Nat) : Loc := .array .modulus j

def ptr (l : Loc) (r t : Reg) : List Instr :=
  match l with
  | .fixed offset => [.mov r (.reg .edi), .alu .add r (.imm (BitVec.ofNat 32 offset))]
  | .array .correction j =>
      [.mov r (.reg .edi), .alu .add r (.imm (BitVec.ofNat 32 (slot 4 j)))]
  | .array w j => VG.Impl.Rsa.X86.KeyRt.arrPtr w.lay r j t

def restore : List Instr := VG.Impl.Rsa.X86.KeyRt.restoreEdi Width.modulus.lay

/-- Clear `k` complete arrays, including both carry words. -/
def clear (w : Width) (k : Nat) : Prog isa :=
  match w with
  | .correction => Dynamic.zerosW hdr (k * 6)
  | _ => VG.Impl.Rsa.X86.KeyRt.zeroArrays w.lay k

def zero (w : Width) (out : Loc) : Prog isa :=
  .seq (.block (ptr out .ebp .edx ++ bytes w .ecx ++
    [.alu .add .ecx (.imm 8), .mov .eax (.imm 0)])) VG.Impl.Bignum.X86.CrtRt.zeroLoop

def copy (w : Width) (out src : Loc) : Prog isa :=
  .seq (.block (ptr src .ebp .edx ++ ptr out .ebx .edx ++ bytes w .edi ++
      [.mov .ecx (.imm (-1))]))
    (.seq VG.Impl.Bignum.X86.CrtRt.selectLoop (.block restore))

def widenTo (target w : Width) (out src : Loc) : Prog isa :=
  .seq (zero target out) (copy w out src)

def widen (w : Width) (out src : Loc) : Prog isa := widenTo .modulus w out src

def small (w : Width) (j : Nat) (x : BitVec 32) : Prog isa :=
  .seq (zero w (.array w j))
    (.block (ptr (.array w j) .ebp .edx ++
      [.mov .eax (.imm x), .store (at_ .ebp 0) .eax]))

def full : VG.Impl.Rsa.X86.KeyRt.Lay := Width.modulus.lay
def sub (o a b : Nat) : Prog isa := VG.Impl.Rsa.X86.KeyRt.sub3 full o a b
def sel (o a b flag : Nat) : Prog isa := VG.Impl.Rsa.X86.KeyRt.sel full o a b flag
def eq (flag a b tmp : Nat) : Prog isa := VG.Impl.Rsa.X86.KeyRt.eqS full flag a b tmp
def cp (o a : Nat) : Prog isa := VG.Impl.Rsa.X86.KeyRt.copy full o a
def cn (j : Nat) (x : BitVec 32) : Prog isa := small .modulus j x

/-- The correction bank has a constant four-word width. -/
def divide (w : Width) : Prog isa :=
  match w with
  | .correction => VG.Impl.RsaKeyGen.X86.Key.divisionCompute 4
  | _ => VG.Impl.Rsa.X86.KeyRt.div w.lay 0 1 2 3

def clearTop (w : Width) (j : Nat) : Prog isa :=
  .block (ptr (.array w j) .ebp .edx ++ bytes w .edx ++
    [.alu .add .ebp (.reg .edx), .mov .eax (.imm 0), .store (at_ .ebp 0) .eax])

def divisionLoad (w : Width) (src divisor : Loc) : Prog isa := seqs [
  clearTop w 2, copy w (.array w 0) src, copy w (.array w 2) divisor]

def divisionStore (w : Width) (quotient remainder : Loc) : Prog isa :=
  .seq (copy w quotient (.array w 0)) (copy w remainder (.array w 1))

def divisionFrom (w : Width) (src divisor quotient remainder : Loc) : Prog isa :=
  .seq (divisionLoad w src divisor) (.seq (divide w) (divisionStore w quotient remainder))

def inverseBank (w : Width) : Prog isa := seqs [
  VG.Impl.Rsa.X86.KeyRt.copy w.lay 1 aM, .block (VG.Impl.Rsa.X86.KeyRt.setOne w.lay 2),
  VG.Impl.Rsa.X86.KeyRt.sub3 w.lay aNM aZero aM]

def inverseLoad (w : Width) (src modulus : Loc) : Prog isa := seqs [
  clear w 15, copy w (.array w 0) src, copy w (.array w aM) modulus]

def inverseSetup (w : Width) (src modulus : Loc) : Prog isa :=
  .seq (inverseLoad w src modulus) (inverseBank w)

def inverseFrom (w : Width) (src modulus : Loc) : Prog isa :=
  .seq (inverseSetup w src modulus) (VG.Impl.Rsa.X86.KeyRt.inverse w.lay)

def gcdIsOne (w : Width) : Prog isa :=
  .seq (small w aT2 1) (VG.Impl.Rsa.X86.KeyRt.eqS w.lay kFlag 1 aT2 aT1)

/-- Combine the comparison borrow and the runtime array's parity. -/
def oddFlag (input : Nat) : List Instr :=
  [.mov .eax (.imm 1), .alu .sub .eax (.reg .ebx)] ++
    ptr (arr input) .ebp .edx ++ [.alu .and .eax (.mem (at_ .ebp 0)),
      .alu .and .eax (.imm 1), .store (sc kFlag) .eax]

/-- Select a valid odd inverse modulus, recording whether the input qualified. -/
def oddModulus (input out : Nat) : Prog isa := seqs [
  cn aT1 3, sub aT2 input aT1, .block (oddFlag input), sel out aT1 input kFlag]

/-- The header word holding a product row's multiplier. -/
def multSlot : Nat := 128

/-- The `left + right + 2` words of `out` zeroed. -/
def productZero (left right : Width) (out : Loc) : Prog isa :=
  .seq (.block (ptr out .ebp .edx ++ bytes left .ecx ++ bytes right .eax ++
    [.alu .add .ecx (.reg .eax), .alu .add .ecx (.imm 8), .mov .eax (.imm 0)])) VG.Impl.Bignum.X86.CrtRt.zeroLoop

/-- Row `i` (`ebp` at word `i` of `out`): word `i` of `a` into the multiplier slot, `ecx` at `b`,
`esi` its bytes and no carry. -/
def productRow (right : Width) (out a b : Loc) : List Instr :=
  ptr out .eax .edx ++ [.mov .ecx (.reg .ebp), .alu .sub .ecx (.reg .eax)] ++
    ptr a .eax .edx ++ [.alu .add .eax (.reg .ecx), .mov .edx (.mem (at_ .eax 0)), .store (sc multSlot) .edx] ++
    ptr b .ecx .edx ++ bytes right .esi ++ [.mov .ebx (.imm 0)]

/-- The row's carry above it, `ebp` at the next row, and ZF after the last. -/
def productNext (left right : Width) (out : Loc) : List Instr :=
  [.store (at_ .ebp 0) .ebx] ++ bytes right .eax ++ [.alu .sub .ebp (.reg .eax), .alu .add .ebp (.imm 4)] ++
    ptr out .eax .edx ++ bytes left .edx ++ [.alu .add .eax (.reg .edx), .alu .cmp .ebp (.reg .eax)]

/-- `[out] = [a] [b]`, `left` and `right` words, one row of `b` for each word of `a`. -/
def product (left right : Width) (out a b : Loc) : Prog isa :=
  .seq (productZero left right out) (.seq (.block (ptr out .ebp .edx))
    (.loop (.seq (.block (productRow right out a b))
      (.seq (VG.Impl.Bignum.X86.CrtRt.rowLoopAt multSlot) (.block (productNext left right out)))) .ne))

def primeProduct (out a b : Nat) : Prog isa := product .prime .prime (arr out) (arr a) (arr b)

def order : Prog isa := seqs [sub aT1 aPa aQa,
  .block [.store (sc kFlag) .ebx], cp aT2 aPa,
  sel aPa aPa aQa kFlag, sel aQa aQa aT2 kFlag]

def decTo (out a : Nat) : Prog isa :=
  seqs [eq kFlag a aZero aT1, sel aT2 aOne aZero kFlag, sub out a aT2]

def primes : Prog isa := seqs [order, decTo aPm aPa, decTo aQm aQa,
  primeProduct aPhi aPm aQm]

def halfIf (j : Nat) : Prog isa := seqs [cp aHalf j,
  .block [.mov .ebx (.imm 0)], VG.Impl.Rsa.X86.KeyRt.half full aHalf,
  sel j j aHalf kFlag]

def bothEven : List Instr :=
  ptr (arr aU) .eax .edx ++ [.mov .ecx (.mem (at_ .eax 0))] ++
  ptr (arr aV) .eax .edx ++ [.alu .or .ecx (.mem (at_ .eax 0)),
    .alu .and .ecx (.imm 1), .alu .xor .ecx (.imm 1), .store (sc kFlag) .ecx]

def halveStep : Prog isa :=
  seqs [.block bothEven, halfIf aU, halfIf aV, halfIf aPhi]

def twoStep : Prog isa :=
  .seq halveStep (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

def twos : Prog isa := seqs [cp aU aPm, cp aV aQm,
  .block (VG.Impl.Rsa.X86.KeyRt.bits full),
  .loop twoStep .ne]

def evenFlag (input : Nat) : Prog isa :=
  .seq (.block (VG.Impl.Rsa.X86.KeyRt.bitOf full kFlag input))
    (.block [.mov .eax (.mem (sc kFlag)), .alu .xor .eax (.imm 1), .store (sc kFlag) .eax])

def oddSecond : Prog isa := seqs [evenFlag aV,
  cp aT1 aU, sel aU aU aV kFlag, sel aV aV aT1 kFlag]

def gcdFrom : Prog isa := seqs [inverseFrom .prime (arr aU) (arr aDen),
  widen .prime (arr aDen) (.array .prime 1), sel aDen aOne aDen kFlag]

def gcdPart : Prog isa := seqs [oddSecond, oddModulus aV aDen, gcdFrom]

def divFull (src divisor quotient remainder : Nat) : Prog isa :=
  divisionFrom .modulus (arr src) (arr divisor) (arr quotient) (arr remainder)

def lcmPart : Prog isa := seqs [twos, gcdPart, divFull aPhi aDen aL aT1]

def lAtLeastTwo : Prog isa := seqs [cn aT1 2, sub aT2 aL aT1,
  .block VG.Impl.RsaKeyGen.X86.Key.borrowMask]

/-- Subtract fixed header pairs before writing either word through EBP. -/
def subtractPair (a b : Nat) : List Instr :=
  [.mov .eax (.mem (sc a)), .mov .edx (.mem (sc (a + 4))),
   .alu .sub .eax (.mem (sc b)), .alu .sbb .edx (.mem (sc (b + 4))),
   .store (at_ .ebp 0) .eax, .store (at_ .ebp 4) .edx]

def complement : Prog isa := .seq (zero .modulus (arr aDen))
  (.block (ptr (arr aDen) .ebp .edx ++ subtractPair kEv (slot 2 3)))

def correctionNumerator : Prog isa := seqs [
  product .exponent .exponent (.array .correction 1) (arr aV) (arr aDen),
  small .correction 2 1,
  Dynamic.chainW .adc 4 (slot 4 0) (slot 4 1) (slot 4 2)]

def correction : Prog isa := seqs [correctionNumerator,
  widenTo .correction .exponent (.array .correction 2) (.fixed kEv), divide .correction,
  widen .exponent (arr aV) (.array .correction 0)]

def dProduct : Prog isa :=
  .seq (product .modulus .exponent (arr 0) (arr aU) (arr aDen))
    (VG.Impl.Rsa.X86.KeyRt.chain full .adc aD 0 aV false)

def dOddPrepare : Prog isa := seqs [divFull aL aE aU aV,
  inverseFrom .exponent (arr aV) (.fixed kEv), gcdIsOne .exponent, lAtLeastTwo]

def dOddFinish : Prog isa := seqs [complement, correction, dProduct]

def dOdd : Prog isa := .seq dOddPrepare dOddFinish

def dEven : Prog isa := seqs [oddModulus aL aDen,
  .block [.mov .eax (.mem (sc kFlag)), .store (sc kOk) .eax],
  divFull aE aDen aU aV, inverseFrom .modulus (arr aV) (arr aDen),
  gcdIsOne .modulus, .block (andS kOk kOk kFlag), cp aD 3]

def dOne : Prog isa := seqs [cp aD aOne, eq kFlag aL aOne aT1,
  .block (VG.Impl.RsaKeyGen.X86.Key.notSlot kOk kFlag)]

def dSelect : Prog isa :=
  .seq (.block (equalExponent 0)) (.ite .e dZero
    (.seq (.block (equalExponent 1)) (.ite .e dOne
      (.seq (.block parityExponent) (.ite .e dEven dOdd)))))

def divisorOf (input : Nat) : Prog isa :=
  seqs [cn aT1 0, eq kFlag input aT1 aT2, sel aDen input aOne kFlag]

def qinvPart : Prog isa := seqs [oddModulus aPa aDen,
  inverseFrom .prime (arr aQa) (arr aDen), gcdIsOne .prime,
  .block (andS kOk kOk kFlag), widen .prime (arr aQi) (.array .prime 3)]

def crtPart : Prog isa := seqs [divisorOf aPm, divFull aD aDen aU aDp,
  divisorOf aQm, divFull aD aDen aU aDq]

def smallConstant : Prog isa := .seq (cn aT1 1)
  (.block (ptr (arr aT1) .ebp .edx ++ bytes .prime .edx ++
    [.alu .add .ebp (.reg .edx), .mov .eax (.imm 1), .store (at_ .ebp 0) .eax]))

def smallMask : Prog isa := seqs [smallConstant, sub aT2 aD aT1,
  .block [.mov .eax (.mem (sc kOk)), .alu .and .eax (.reg .ebx), .alu .cmp .eax (.imm 0)]]

def withFlag (c : Prog isa) : Prog isa := .seq c (.block (andS kOk kOk kFlag))

def topBit : List Instr := ptr (arr aN) .ebp .edx ++ bytes .modulus .edx ++
  [.alu .add .ebp (.reg .edx), .alu .sub .ebp (.imm 4), .mov .eax (.mem (at_ .ebp 0)),
   .shift .shr .eax 31, .store (sc kFlag) .eax]

def exponentAtLeastThree : Prog isa := seqs [cn aT1 3, sub aT2 aE aT1,
  .block [.mov .eax (.mem (sc kOk)), .store (sc kFlag) .eax], .block borrowMask]

def finalMask : Prog isa := seqs [withFlag (.block topBit),
  withFlag (.block (VG.Impl.Rsa.X86.KeyRt.bitOf full kFlag aPa)),
  withFlag (.block (VG.Impl.Rsa.X86.KeyRt.bitOf full kFlag aQa)),
  withFlag (.block (VG.Impl.Rsa.X86.KeyRt.bitOf full kFlag aE)),
  withFlag (.block exponentUpper), exponentAtLeastThree]

def keyPart : Prog isa := seqs [qinvPart, crtPart, primeProduct aN aPa aQa, finalMask,
  .block [.mov .eax (.mem (sc kOk)), .store (sc kStatus) .eax]]

def prepareLoaded : Prog isa := seqs [primes, lcmPart, dSelect]

def deriveLoaded : Prog isa :=
  .seq prepareLoaded (.seq smallMask (.ite .ne retry keyPart))

/-- Argument `i` of the cdecl call (`p` is 4, `q` 6, `e` 14 and its length 15). -/
def argument (i : Nat) : MemOp := VG.Impl.Bignum.X86.PublicFn.argument (i + 4)

/-- Every array cleared, and one. -/
def clearInputs : Prog isa := .seq (clear .modulus VG.Impl.RsaKeyGen.X86.Key.nArr) (cn aOne 1)

/-- The prime at argument `arg` imported into array 0 at the prime width, then widened into `out`. -/
def loadPrime (arg out : Nat) : Prog isa := seqs [
  .block ([.mov .esi (.mem (argument arg))] ++ ptr (arr 0) .ebx .edx ++ bytes .prime .ecx ++
    [.alu .add .ebx (.reg .ecx), .alu .sub .ebx (.imm 4), .shift .shr .ecx 2]),
  VG.Impl.RsaKeyGen.X86.Import.code, widen .prime (arr out) (arr 0)]

/-- The exponent into its header words, then widened into its array. -/
def loadExponent : Prog isa := seqs [
  .block [.mov .esi (.mem (argument 14)), .mov .ecx (.mem (argument 15))],
  VG.Impl.Bignum.X86.loadBE 1 VG.Impl.RsaKeyGen.X86.Key.kEv,
  widen .exponent (arr aE) (.fixed VG.Impl.RsaKeyGen.X86.Key.kEv)]

/-- The inputs at the run-time width. -/
def loadInputs : Prog isa := seqs [clearInputs, loadPrime 4 aPa, loadPrime 6 aQa, loadExponent]

/-- Array `j` zeroed unless the key was accepted, then `ebx` and `ecx` the pointer and length
at arguments `pointer` and `length`, and `esi` the array's last byte to store. -/
def arraySetup (j pointer length : Nat) : Prog isa :=
  .seq (sel j aZero j VG.Impl.RsaKeyGen.X86.Key.kOk)
    (.block ([.mov .ebx (.mem (argument pointer)), .mov .ecx (.mem (argument length))] ++
      ptr (arr j) .esi .edx ++ [.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]))

/-- Array `j`, or zero unless the key was accepted, stored big-endian through the pointer and
length at arguments `pointer` and `length`. -/
def writeArray (j pointer length : Nat) : Prog isa :=
  .seq (arraySetup j pointer length) VG.Impl.Bignum.X86.reverseBytes

def writePort (i : Nat) : Prog isa :=
  writeArray (VG.Impl.RsaKeyGen.X86.Key.outputIndex i) (2 * i) (2 * i + 1)

def writePorts : Nat → Nat → Prog isa
  | _, 0 => .block []
  | i, count + 1 => .seq (writePort i) (writePorts (i + 1) count)

/-- The zero array rebuilt, the seven outputs, and the status. -/
def writeOutputs : Prog isa := seqs [zero .modulus (arr aZero), writePorts 0 7,
  .block [.mov .eax (.mem (sc VG.Impl.RsaKeyGen.X86.Key.kStatus))]]

def front : Prog isa := .seq loadInputs (.seq deriveLoaded writeOutputs)

def body : Prog isa := .seq VG.Impl.RsaKeyGen.X86.Key.enter front

def code : Prog isa := .frame (.push [.ebx, .ebp, .esi, .edi])
  (.seq body (.block Compact.restoreRegs)) (.pop .ebx 4)

end VG.Impl.RsaKeyGen.X86.KeyRuntime
