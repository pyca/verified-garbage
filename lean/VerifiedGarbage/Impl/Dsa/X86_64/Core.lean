module

public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic

/-!
# DSA signing and verification arithmetic on x86-64

The core is called after workspace setup and public parameter checks. It
always evaluates every secret-dependent arithmetic operation. Range checks,
the key-consistency mask, final comparison and output masking belong to the
entry points; these internal programs are not separately exposed as APIs.

Scalar buffers use the caller's q_len, including leading-zero padding.
The digest operand uses the public min(digest_len, bitLength(q)/8).
-/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.Core

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout

/-- A saved field at the outer workspace base. -/
def field (f : Field) : MemOp := { base := .rdi, disp := f.offset }

/-- Operand pointer in rax. The current workspace is the outer workspace. -/
def pointer : Pointer → List Instr
  | .input f => [.mov .rax (.mem (field f))]
  | .local offset => [.mov .rax (.reg .rdi), .alu .add .rax (.imm (BitVec.ofNat 32 offset))]
  | .signatureS => [.mov .rax (.mem (field .signature)), .alu .add .rax (.mem (field .qLen))]

/-- Store a pointer and its public byte length in the call header. -/
def operand (slot lenSlot : Nat) (value : Operand) : List Instr :=
  pointer value.pointer ++
    ([.store (hdr slot) .rax, .mov .rax (.mem (field value.length)), .store (hdr lenSlot) .rax] : List Instr)

/-- Enter the p or q workspace at its fixed offset. -/
def enter (offset : Nat) : List Instr := [.alu .add .rdi (.imm (BitVec.ofNat 32 offset))]

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

/-- Compute the verification value into u; the caller compares it with r
and combines that equality with parameter, key and scalar-range checks. -/
def verify (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  pow mul qWorkspace signatureS (scalar qMinusTwo) (scalar inverse),
  reduce mul digest (scalar z),
  product mul qWorkspace (scalar z) (scalar inverse) (scalar u),
  product mul qWorkspace signatureR (scalar inverse) (scalar v),
  pow mul pWorkspace generator (scalar u) (element t),
  pow mul pWorkspace publicValue (scalar v) (element t2),
  product mul pWorkspace (element t) (element t2) (element t),
  reduce mul (element t) (scalar u)]

end VG.Impl.Dsa.X86_64.Core
