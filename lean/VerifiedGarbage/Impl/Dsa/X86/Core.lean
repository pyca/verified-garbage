module

public import VerifiedGarbage.Impl.Dsa.X86.Layout
public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Impl.Dsa.X86.Stream
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Impl.Dsa.X86.Arith

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

def load (n len dst : Nat) (p : Pointer) : Prog isa :=
  .seq (.block (pointer p)) (loadComponent len n dst)

/-- Every operation restores its modulus and Montgomery constants. -/
def setup (len : Nat) (modulus : Field) : Prog isa :=
  .seq (load ((len + 7) / 8) len (slot ((len + 7) / 8) 0) (.input modulus))
    (contextSetup ((len + 7) / 8))

/-- Internal results are not masked until final signature output. -/
def store (len output : Nat) : Prog isa :=
  .seq (.block (pointer (.local output) ++ [.mov .ecx (.imm (BitVec.allOnes 32))]))
    (storeComponent len (slot ((len + 7) / 8) 6))

/-- Common byte input staging for ordinary and retained-context exponentiation. -/
def loadPower (n len expLen : Nat) (modulus : Field) (a e : Pointer) : Prog isa :=
  .seq (load n len (slot n 0) (.input modulus))
    (.seq (load n len (slot n 5) a) (load n expLen (slot n 8) e))

def power (len expLen : Nat) (modulus : Field) (a e : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (load n len (slot n 0) (.input modulus))
  (.seq (.seq (load n len (slot n 5) a) (load n expLen (slot n 8) e))
  (.seq (Pow.call n ((expLen + 3) / 4)) (store len output)))

/-- The staging of the product of two powers (`Pow.core2`): `loadPower`'s,
then the second base into slot 7 and the second exponent after the first. -/
def loadPower2 (n len expLen : Nat) (modulus : Field) (a e a2 e2 : Pointer) : Prog isa :=
  .seq (loadPower n len expLen modulus a e)
    (.seq (load n len (slot n 7) a2) (load n expLen (Pow.exp2 n) e2))

/-- `a^e · a2^e2 mod m`, in one pass over both exponents (`Pow.core2`). -/
def power2 (len expLen : Nat) (modulus : Field) (a e a2 e2 : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (loadPower2 n len expLen modulus a e a2 e2)
    (.seq (Pow.core2 n ((expLen + 3) / 4)) (store len output))

/-- `a b mod m` by a call of the width's shared product (`Arith.mulCall`). -/
def productMod (len : Nat) (modulus : Field) (a b : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (loadPower n len len modulus a b) (.seq (Arith.mulCall n) (store len output))

def product (len : Nat) (a b : Pointer) (output : Nat) : Prog isa :=
  productMod len .q a b output

def sum (len : Nat) (a b : Pointer) (output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (setup len .q)
  (.seq (.seq (load n len (slot n 5) a) (load n len (slot n 8) b))
  (.seq (ordinaryAdd n) (store len output)))

/-- Reduce `len` bytes (an immediate, or a saved public length) at `input`
modulo q, by a call of the width's shared reduction (`Arith.reduceCall`). -/
def reduce (qLen : Nat) (len : Src) (input : Pointer) (output : Nat) : Prog isa :=
  let n := (qLen + 7) / 8
  .seq (load n qLen (slot n 0) (.input .q))
  (.seq (.block (pointer input ++ [.mov .ebx len]))
  (.seq (Arith.reduceCall n) (store qLen output)))

/-- The digest prefix the shape check saved. -/
def digestPrefix : Src := .mem (sc (Layout.field .digestPrefixLen))

/-- Compute r and s, retaining all range/key checks in the caller's mask. -/
def signStart (pLen qLen : Nat) : Prog isa := sequence [
  power pLen qLen .p (.input .g) (.input .nonce) t,
  reduce qLen (.imm (BitVec.ofNat 32 pLen)) (.local t) r,
  power qLen qLen .q (.input .nonce) (.local qMinusTwo) inverse]

def signFinish (qLen : Nat) : Prog isa := sequence [
  product qLen (.input .x) (.local r) u,
  reduce qLen digestPrefix (.input .digest) z,
  sum qLen (.local z) (.local u) v,
  product qLen (.local inverse) (.local v) s]

def sign (pLen qLen : Nat) : Prog isa :=
  .seq (signStart pLen qLen) (signFinish qLen)

/-- Verification's scalars: `w = s⁻¹`, `u = z w` and `v = r w`, modulo q. -/
def verifyScalars (qLen : Nat) : Prog isa := sequence [
  power qLen qLen .q .signatureS (.local qMinusTwo) inverse,
  reduce qLen digestPrefix (.input .digest) z,
  product qLen (.local z) (.local inverse) u,
  product qLen (.input .signature) (.local inverse) v]

/-- `g^u y^v mod p`, as one product of two powers, then modulo q. -/
def verifyPowers (pLen qLen : Nat) : Prog isa := sequence [
  power2 pLen qLen .p (.input .g) (.local u) (.input .y) (.local v) t,
  reduce qLen (.imm (BitVec.ofNat 32 pLen)) (.local t) u]

def verify (pLen qLen : Nat) : Prog isa :=
  .seq (verifyScalars qLen) (verifyPowers pLen qLen)

end VG.Impl.Dsa.X86.Core
