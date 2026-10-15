module

public import VerifiedGarbage.Impl.Dsa.X86.Layout
public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
public import VerifiedGarbage.Impl.Dsa.X86.Bytes

/-! # DSA arithmetic composition on x86

These internal programs run after public domain checks. All secret operands
are processed regardless of the accumulated validity mask. Intermediate
values use big-endian buffers outside the reused Montgomery context.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Core
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout

def sequence (ps : List (Prog isa)) : Prog isa := ps.foldr .seq (.block [])

def pointer : Pointer → List Instr
  | .input f => [.mov .esi (.mem (sc (Layout.field f)))]
  | .local offset => [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 offset))]
  | .signatureS => [.mov .esi (.mem (sc (Layout.field .signature))),
      .alu .add .esi (.mem (sc (Layout.field .qLen)))]

def load (n len dst : Nat) (p : Pointer) : List Instr :=
  pointer p ++ loadComponent len n dst

/-- Every operation restores its modulus and Montgomery constants. -/
def setup (len : Nat) (modulus : Field) : Prog isa :=
  .seq (.block (load ((len + 7) / 8) len (slot ((len + 7) / 8) 0) (.input modulus)))
    (contextSetup ((len + 7) / 8))

/-- Internal results are not masked until final signature output. -/
def store (n len output : Nat) : List Instr :=
  pointer (.local output) ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] : List Instr) ++
    storeComponent len n (slot n 6)

def power (len expLen : Nat) (modulus : Field) (a e : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (setup len modulus)
  (.seq (.block (load n len (slot n 5) a ++ load n expLen (slot n 8) e))
  (.seq (exponentiate n ((expLen + 3) / 4)) (.block (store n len output))))

def productMod (len : Nat) (modulus : Field) (a b : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (setup len modulus)
  (.seq (.block (load n len (slot n 5) a ++ load n len (slot n 8) b))
  (.seq (ordinaryMul n) (.block (store n len output))))

def product (len : Nat) (a b : Pointer) (output : Nat) : Prog isa :=
  productMod len .q a b output

def sum (len : Nat) (a b : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (setup len .q)
  (.seq (.block (load n len (slot n 5) a ++ load n len (slot n 8) b))
  (.seq (.block (ordinaryAdd n)) (.block (store n len output))))

def reduce (qLen inputLen : Nat) (input : Pointer) (output : Nat) : Prog isa :=
  let n := (qLen + 7) / 8
  .seq (setup qLen .q)
  (.seq (.block (pointer input ++ [.store (sc sourcePointer) .esi]))
  (.seq (reduceStream n inputLen) (.block (store n qLen output))))

/-- Compute r and s, retaining all range/key checks in the caller's mask. -/
def signStart (pLen qLen : Nat) : Prog isa := sequence [
  power pLen qLen .p (.input .g) (.input .nonce) t,
  reduce qLen pLen (.local t) r,
  power qLen qLen .q (.input .nonce) (.local qMinusTwo) inverse]

def signFinish (qLen digestLen : Nat) : Prog isa := sequence [
  product qLen (.input .x) (.local r) u,
  reduce qLen digestLen (.input .digest) z,
  sum qLen (.local z) (.local u) v,
  product qLen (.local inverse) (.local v) s]

def sign (pLen qLen digestLen : Nat) : Prog isa :=
  .seq (signStart pLen qLen) (signFinish qLen digestLen)

/-- Verification uses two fixed-iteration powers and a product modulo p. -/
def verifyScalars (qLen digestLen : Nat) : Prog isa := sequence [
  power qLen qLen .q .signatureS (.local qMinusTwo) inverse,
  reduce qLen digestLen (.input .digest) z,
  product qLen (.local z) (.local inverse) u,
  product qLen (.input .signature) (.local inverse) v]

def verifyPowers (pLen qLen : Nat) : Prog isa := sequence [
  power pLen qLen .p (.input .g) (.local u) t,
  power pLen qLen .p (.input .y) (.local v) t2,
  productMod pLen .p (.local t) (.local t2) t,
  reduce qLen pLen (.local t) u]

def verify (pLen qLen digestLen : Nat) : Prog isa :=
  .seq (verifyScalars qLen digestLen) (verifyPowers pLen qLen)

end VG.Impl.Dsa.X86.Core
