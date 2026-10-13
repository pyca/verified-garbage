module

public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic

/-!
# DSA signing and verification arithmetic on AArch64

As x86-64's (`Impl/Dsa/X86_64/Core.lean`): the core is called after
workspace setup and public parameter checks, and always evaluates every
secret-dependent arithmetic operation. Range checks, the key-consistency
mask, final comparison and output masking belong to the entry points.

The outer workspace's base is in `x0`. An operation stores its operands'
pointers and lengths in the outer header, enters the `p` or `q` workspace
(`x0` its base), and returns to the outer workspace by the child's link.
Scalar buffers use the caller's q_len, including leading-zero padding.
The digest operand uses the public min(digest_len, bitLength(q)/8).
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Core

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout

/-- A saved field of the outer workspace into `t`. -/
def field (t : Reg) (f : Field) : Instr := .ldr .x t .x0 f.offset

/-- Operand pointer in `x3`. The current workspace is the outer workspace. -/
def pointer : Pointer → List Instr
  | .input f => [field .x3 f]
  | .local offset => [.movz .x .x3 (BitVec.ofNat 16 offset) 0, .add .x .x3 .x0 .x3]
  | .signatureS => [field .x3 .signature, field .x4 .qLen, .add .x .x3 .x3 .x4]

/-- Store a pointer and its public byte length in the call header. -/
def operand (slot lenSlot : Nat) (value : Operand) : List Instr :=
  pointer value.pointer ++ ([sth .x3 slot, field .x3 value.length, sth .x3 lenSlot] : List Instr)

/-- Enter the p or q workspace at its fixed offset. -/
def enter (offset : Nat) : List Instr := [.movz .x .x3 (BitVec.ofNat 16 offset) 0, .add .x .x0 .x0 .x3]

/-- Return to the outer workspace after writing an arithmetic result. -/
def finish : List (Prog isa) := [Arithmetic.store aY result resultLen, .block [Crt.leave]]

def pow (mul : Nat → Nat → Nat → Prog isa) (ws : Nat) (base exponent output : Operand) : Prog isa :=
  seqs ([.block (operand arg argLen base ++ operand arg2 arg2Len exponent ++
    operand result resultLen output ++ enter ws),
    Arithmetic.power mul arg argLen arg2 arg2Len] ++ finish)

def product (mul : Nat → Nat → Nat → Prog isa) (ws : Nat) (a b output : Operand) : Prog isa :=
  seqs ([.block (operand arg argLen a ++ operand arg2 arg2Len b ++
    operand result resultLen output ++ enter ws),
    Arithmetic.product mul arg argLen arg2 arg2Len] ++ finish)

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

/-- Compute the verification value into u: g^u1 and y^u2 separately, their
product, reduced modulo q. The caller compares it with r and combines that
equality with parameter, key and scalar-range checks. -/
def verify (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  pow mul qWorkspace signatureS (scalar qMinusTwo) (scalar inverse),
  reduce mul digest (scalar z),
  product mul qWorkspace (scalar z) (scalar inverse) (scalar u),
  product mul qWorkspace signatureR (scalar inverse) (scalar v),
  pow mul pWorkspace generator (scalar u) (element t),
  pow mul pWorkspace publicValue (scalar v) (element t2),
  product mul pWorkspace (element t) (element t2) (element t),
  reduce mul (element t) (scalar u)]

end VG.Impl.Dsa.AArch64.Core
