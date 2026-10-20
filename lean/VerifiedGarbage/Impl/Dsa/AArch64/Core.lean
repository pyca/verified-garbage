module

public import VerifiedGarbage.Impl.Dsa.AArch64.Joint
public import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower

/-!
# DSA signing and verification arithmetic on AArch64

The core is called after workspace setup and public parameter checks. It
always evaluates every secret-dependent arithmetic operation. Range checks,
the key-consistency mask, final comparison and output masking belong to the
entry points; these internal programs are not separately exposed as APIs.

Scalar buffers use the caller's q_len, including leading-zero padding.
The digest operand uses the public min(digest_len, bitLength(q)/8).
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Core

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout

/-- Load a saved field from the outer workspace. -/
def field (dst : Reg) (f : Field) : Instr := .ldr .x dst .x0 f.offset

/-- Resolve an operand into x3, using x4 for the second signature offset. -/
def pointer : Pointer → List Instr
  | .input f => [field .x3 f]
  | .local offset => [movi .x3 offset, .add .x .x3 .x0 .x3]
  | .signatureS => [field .x3 .signature, field .x4 .qLen, .add .x .x3 .x3 .x4]

def operand (slot lenSlot : Nat) (value : Operand) : List Instr :=
  pointer value.pointer ++ [sth .x3 slot, field .x3 value.length, sth .x3 lenSlot]

def enter (offset : Nat) : List Instr := [movi .x4 offset, .add .x .x0 .x0 .x4]

/-- Return to the outer workspace after writing an arithmetic result. -/
def finish : List (Prog isa) := [Arithmetic.store aY result resultLen, .block [Crt.leave]]

def pow (mul : Nat → Nat → Nat → Prog isa) (ws : Nat) (base exponent output : Operand) : Prog isa :=
  seqs ([.block (operand arg argLen base ++ operand arg2 arg2Len exponent ++
    operand result resultLen output ++ enter ws),
    Arithmetic.power mul arg argLen arg2 arg2Len] ++ finish)

/-- Only for exponents declared public by the caller's contract. -/
def publicPow (mul : Nat → Nat → Nat → Prog isa) (ws : Nat) (base exponent output : Operand) : Prog isa :=
  seqs ([.block (operand arg argLen base ++ operand arg2 arg2Len exponent ++
    operand result resultLen output ++ enter ws),
    PublicPower.power mul arg argLen arg2 arg2Len] ++ finish)

def product (mul : Nat → Nat → Nat → Prog isa) (ws : Nat) (a b output : Operand) : Prog isa :=
  seqs ([.block (operand arg argLen a ++ operand arg2 arg2Len b ++
    operand result resultLen output ++ enter ws),
    Arithmetic.product mul arg argLen arg2 arg2Len] ++ finish)

/-- `g^u y^v` for verification's scalars `u` and `v` (`Joint.power`). -/
def joint (mul : Nat → Nat → Nat → Prog isa) (ws : Nat) (a b output : Operand) : Prog isa :=
  seqs ([.block (operand arg argLen a ++ operand arg2 arg2Len b ++
    operand result resultLen output ++ enter ws), Joint.power mul] ++ finish)

def reduce (mul : Nat → Nat → Nat → Prog isa) (input output : Operand) : Prog isa :=
  seqs ([.block (operand arg argLen input ++ operand result resultLen output ++ enter qWorkspace),
    Arithmetic.reduce mul arg argLen] ++ finish)

/-- Addition of two ordinary, already reduced scalar operands. -/
def add (a b output : Operand) : Prog isa :=
  seqs ([.block (operand arg argLen a ++ operand arg2 arg2Len b ++
    operand result resultLen output ++ enter qWorkspace),
    Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len,
    Crt.addMod aY aX aXm] ++ finish)

def scalar (offset : Nat) : Operand := ⟨.local offset, .qLen⟩
def element (offset : Nat) : Operand := ⟨.local offset, .pLen⟩
def generator : Operand := ⟨.input .g, .pLen⟩
def publicValue : Operand := ⟨.input .y, .pLen⟩
def privateScalar : Operand := ⟨.input .x, .qLen⟩
def nonce : Operand := ⟨.input .nonce, .qLen⟩
def signatureR : Operand := ⟨.input .signature, .qLen⟩
def signatureS : Operand := ⟨.signatureS, .qLen⟩
def digest : Operand := ⟨.input .digest, .digestPrefixLen⟩

/-- Compute the signature into r and s. Rejected scalar inputs are still
processed; the caller combines their range masks with r/s nonzero masks. -/
def sign (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  pow mul pWorkspace generator nonce (element t),
  reduce mul (element t) (scalar r),
  pow mul qWorkspace nonce (scalar qMinusTwo) (scalar inverse),
  product mul qWorkspace privateScalar (scalar r) (scalar u),
  reduce mul digest (scalar z),
  add (scalar z) (scalar u) (scalar v),
  product mul qWorkspace (scalar inverse) (scalar v) (scalar s)]

/-- Compute the verification value into u: `g^u y^v` by one joint
exponentiation, reduced modulo q. The caller compares it with r
and combines that equality with parameter, key and scalar-range checks. -/
def verify (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  pow mul qWorkspace signatureS (scalar qMinusTwo) (scalar inverse),
  reduce mul digest (scalar z),
  product mul qWorkspace (scalar z) (scalar inverse) (scalar u),
  product mul qWorkspace signatureR (scalar inverse) (scalar v),
  joint mul pWorkspace generator publicValue (element t),
  reduce mul (element t) (scalar u)]

end VG.Impl.Dsa.AArch64.Core
