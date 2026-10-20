module

public import VerifiedGarbage.Impl.Dsa.Arm.Layout
public import VerifiedGarbage.Impl.Dsa.Arm.Arith
public import VerifiedGarbage.Impl.Dsa.Arm.Bytes

/-! # DSA arithmetic composition on 32-bit ARM

These internal programs run after public domain checks. All secret operands
are processed regardless of the accumulated validity mask. Intermediate
values use big-endian buffers outside the reused Montgomery context.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Core
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic
open VG.Impl.Dsa.Layout

def sequence (ps : List (Prog isa)) : Prog isa := ps.foldr .seq (.block [])

/-- `r11` = the operand's address. -/
def pointer : Pointer → List Instr
  | .input f => [.ldr .r11 .r12 (Layout.field f)]
  | .local offset => ptr .r11 offset
  | .signatureS => [.ldr .r11 .r12 (Layout.field .signature), .ldr .r4 .r12 (Layout.field .qLen),
      .dp .add .r11 .r11 (.reg .r4)]

def load (n len dst : Nat) (p : Pointer) : Prog isa :=
  .seq (.block (pointer p)) (loadComponent len n dst)

/-- Every operation restores its modulus and Montgomery constants. -/
def setup (len : Nat) (modulus : Field) : Prog isa :=
  .seq (load ((len + 7) / 8) len (modS ((len + 7) / 8)) (.input modulus)) (Context.call ((len + 7) / 8))

/-- Internal results are not masked until the final signature output. -/
def store (len output : Nat) : Prog isa :=
  .seq (.block (pointer (.local output) ++ allOnes ++ [.mov .r3 (.reg .r4)]))
    (storeComponent len (resS ((len + 7) / 8)))

/-- The modulus, the base and the exponent, then a call of
`vg_dsa_pow_{n}_{e}` (`Pow.lean`), which sets up their context itself. -/
def power (len expLen : Nat) (modulus : Field) (a e : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (load n len (modS n) (.input modulus))
  (.seq (.seq (load n len (baseS n) a) (load n expLen (expS n) e))
  (.seq (Pow.call n ((expLen + 3) / 4)) (store len output)))

/-- As `power`, calling `vg_dsa_mulmod_{n}` (`Arith.lean`). -/
def productMod (len : Nat) (modulus : Field) (a b : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (load n len (modS n) (.input modulus))
  (.seq (.seq (load n len (baseS n) a) (load n len (expS n) b))
  (.seq (Arith.mulCall n) (store len output)))

def product (len : Nat) (a b : Pointer) (output : Nat) : Prog isa :=
  productMod len .q a b output

def sum (len : Nat) (a b : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (setup len .q)
  (.seq (.seq (load n len (baseS n) a) (load n len (expS n) b))
  (.seq (ordinaryAdd n) (store len output)))

/-- The byte count of a reduction: an immediate, or a saved public length. -/
inductive Count where
  | imm (len : Nat)
  | field (f : Field)
  deriving DecidableEq, Repr

/-- `lr = r11 + count`. -/
def countEnd : Count → List Instr
  | .imm len => [.movw .lr (BitVec.ofNat 16 len), .dp .add .lr .lr (.reg .r11)]
  | .field f => [.ldr .lr .r12 (Layout.field f), .dp .add .lr .lr (.reg .r11)]

/-- Reduce `count` bytes at `input` modulo q, by a call of `vg_dsa_reduce_{n}`. -/
def reduce (qLen : Nat) (count : Count) (input : Pointer) (output : Nat) : Prog isa :=
  let n := (qLen + 7) / 8
  .seq (load n qLen (modS n) (.input .q))
  (.seq (.block (pointer input ++ countEnd count))
  (.seq (Arith.reduceCall n) (store qLen output)))

/-- The digest prefix the shape check saved. -/
def digestPrefix : Count := .field .digestPrefixLen

/-- Compute r and s, retaining all range/key checks in the caller's mask. -/
def signStart (pLen qLen : Nat) : Prog isa := sequence [
  power pLen qLen .p (.input .g) (.input .nonce) t,
  reduce qLen (.imm pLen) (.local t) r,
  power qLen qLen .q (.input .nonce) (.local qMinusTwo) inverse]

def signFinish (qLen : Nat) : Prog isa := sequence [
  product qLen (.input .x) (.local r) u,
  reduce qLen digestPrefix (.input .digest) z,
  sum qLen (.local z) (.local u) v,
  product qLen (.local inverse) (.local v) s]

def sign (pLen qLen : Nat) : Prog isa :=
  .seq (signStart pLen qLen) (signFinish qLen)

/-- Verification uses two fixed-iteration powers and a product modulo p. -/
def verifyScalars (qLen : Nat) : Prog isa := sequence [
  power qLen qLen .q .signatureS (.local qMinusTwo) inverse,
  reduce qLen digestPrefix (.input .digest) z,
  product qLen (.local z) (.local inverse) u,
  product qLen (.input .signature) (.local inverse) v]

def verifyPowers (pLen qLen : Nat) : Prog isa := sequence [
  power pLen qLen .p (.input .g) (.local u) t,
  power pLen qLen .p (.input .y) (.local v) t2,
  productMod pLen .p (.local t) (.local t2) t,
  reduce qLen (.imm pLen) (.local t) u]

def verify (pLen qLen : Nat) : Prog isa :=
  .seq (verifyScalars qLen) (verifyPowers pLen qLen)

end VG.Impl.Dsa.Arm.Core
