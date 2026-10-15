module

public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Impl.Ffdh.X86_64.Exchange

/-! # One FFDH key-generation attempt on x86-64 -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Domain.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open Crt (ws stk leave loadArr)

/-- `(x, x_len, y, y_len, domain, domain_len, p_len, rand, rand_len,
scratch, scratch_len)`: preserve the outputs and the random source in the outer header. -/
def entry : List Instr :=
  [.mov .rax (.mem (stk 4)), .mov .r10 (.mem (stk 1)), .mov .r11 (.mem (stk 2))] ++ save .rax ++
  [.store (ws .rax sX) .rdi, .store (ws .rax sY) .rdx, .store (ws .rax sDom) .r8,
    .store (ws .rax sDomLen) .r9, .store (ws .rax sK) .r10, .store (ws .rax sRand) .r11,
    .mov .rdi (.reg .rax)]

/-- Scan q, or p when q is absent: p and p-1 have the same bit length for
an odd modulus above 1. The first byte is returned in rax. -/
def bound : List (Prog isa) := [.block qTest, .ite .e (seqs (scan sDom)) (seqs (scan sQ))]

/-- The low bits through the first byte's highest bit, including the all-zero case. -/
def smear : List Instr :=
  [.mov .rdx (.reg .rax), .shift .shr .rdx 1, .alu .or .rax (.reg .rdx),
    .mov .rdx (.reg .rax), .shift .shr .rdx 2, .alu .or .rax (.reg .rdx),
    .mov .rdx (.reg .rax), .shift .shr .rdx 4, .alu .or .rax (.reg .rdx), .store (hdr sMsk) .rax]

/-- One random byte to x: zero before the bound's first byte, masked at it,
and retained afterwards. Both conditional moves depend only on the public index. -/
def cutBody : List Instr :=
  [.movzx8 .rax (at0 .r10), .alu .cmp .rcx (.reg .r8), .mov32 .rdx (.imm 255), .mov32 .rbx (.imm 0),
    .cmov .b .rdx (.reg .rbx), .cmov .e .rdx (.reg .r9), .alu .and .rax (.reg .rdx),
    .store8 (at0 .r11) .rax, .alu .add .r10 (.imm 1), .alu .add .r11 (.imm 1),
    .alu .add .rcx (.imm 1), .alu .sub .r14 (.imm 1)]

/-- Load the public cut position and width, and the two byte pointers. -/
def cutSetup : List Instr :=
  [.mov .r10 (.mem (hdr sRand)), .mov .r11 (.mem (hdr sX)), .mov .r9 (.mem (hdr sMsk)),
    .mov .r8 (.mem (hdr sK)), .alu .sub .r8 (.mem (hdr sEl)), .mov32 .rcx (.imm 0),
    .mov .r14 (.mem (hdr sK))]

/-- Retain the public significant slice of the sampled exponent. -/
def cutFinish : List Instr :=
  [.mov .rax (.mem (hdr sX)), .alu .add .rax (.reg .r8), .store (hdr sX) .rax,
    .mov .rax (.mem (hdr sEl)), .store (hdr sXl) .rax]

/-- Cut the random bytes to the bound's bit length, then retain only its
public number of significant bytes as the exponentiation input. -/
def scalar : List (Prog isa) := bound ++ [
  .block smear, .block cutSetup, .loop (.block cutBody) .ne, .block cutFinish]

/-- Move the output pointer to exchange's output slot and the checked
generator to its input slot. The inner modulus workspace stays active. -/
def bridge : List Instr :=
  [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (ws .rax sY)), .store (ws .rax sOut) .rdx,
    .mov .rdx (.mem (ws .rax sG)), .store (ws .rax sY) .rdx]

/-- Mask one scalar-output octet; only the public byte count controls the loop. -/
def maskBody : List Instr :=
  [.movzx8 .rax (at0 .r11), .alu .and .rax (.reg .r15), .store8 (at0 .r11) .rax,
    .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]

/-- Preserve the status and reconstruct x's full-width output pointer. -/
def maskSetup : List Instr :=
  [.store (hdr sF) .rax, .mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax),
    .mov .r11 (.mem (hdr sX)), .mov .rdx (.mem (hdr sK)), .alu .sub .rdx (.mem (hdr sXl)),
    .alu .sub .r11 (.reg .rdx), .mov .rcx (.mem (hdr sK))]

/-- Mask the full scalar output with the returned range flag. -/
def maskX : Prog isa := .seq (.block maskSetup) (.loop (.block maskBody) .ne)

/-- Range-check the generated value and store its masked octets through the
exchange implementation's existing output path. -/
def publicOutput : List (Prog isa) := [.block bridge] ++ range aY ++
  [.block Exchange.finBlk, storeBE, .block [.mov .rax (.mem (hdr sF)), leave]]

/-- Convert the saved success flag to key-generation status 1 or 3. -/
def status : List Instr :=
  [.mov .rax (.mem (hdr sF)), .shift .shl .rax 1, .mov32 .rdx (.imm 3),
    .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx)]

variable (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) (r2 : Prog isa)

/-- The valid scalar's public value, using generator subgroup closure;
exchange's proven range check and masked store encode it or zero it. -/
def tail : List (Prog isa) := [r2] ++ pow mul ex sG sK sX sXl ++ publicOutput ++ [maskX, .block status]

/-- Check the sampled scalar, then derive its public value or clear the outputs. -/
def core : List (Prog isa) := [.block head] ++ pSetup ++ loadArr aXm sX sXl ++
  CheckPrivate.scalarRange ++ [.block [.alu .test .rax (.reg .rax)],
    .ite .e (seqs [.block [leave], maskX, ret 2]) (seqs (tail mul ex r2))]

def main : Prog isa := seqs ([Keys.zeroOut sY sK] ++ scalar ++ core mul ex r2)

def body : Prog isa := .seq (.block (entry ++ domHead)) (.ite .ne (ret 0) (main mul ex r2))

def code : Prog isa := .seq (body mul ex r2) (.block exit)

end VG.Impl.Ffdh.X86_64.Domain.GenerateKey
