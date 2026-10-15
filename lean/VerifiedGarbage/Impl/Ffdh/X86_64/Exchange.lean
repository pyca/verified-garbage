module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain

/-! # FFDH exchange on x86-64 -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Domain.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open Crt (ws stk leave)

/-- System V arguments: `(out, out_len, domain, domain_len, p_len, x,
x_len, peer, peer_len, scratch, scratch_len)`. Save the ABI registers in
scratch and the input pointers in its outer header. -/
def entry : List Instr :=
  [.mov .rax (.mem (stk 4)), .mov .r10 (.mem (stk 1)), .mov .r11 (.mem (stk 2))] ++ save .rax ++
  [.store (ws .rax sOut) .rdi, .store (ws .rax sDom) .rdx, .store (ws .rax sDomLen) .rcx,
    .store (ws .rax sK) .r8, .store (ws .rax sX) .r9,
    .store (ws .rax sXl) .r10, .store (ws .rax sY) .r11, .mov .rdi (.reg .rax)]

/-- The output's pointers and length, and a mask from the range check.
The flag remains in the inner header while the bytes are stored. -/
def finBlk : List Instr :=
  [.mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax),
    .mov .rbx (.mem (hdr (sArr aY))), .mov .rax (.mem (hdr Crt.sLink)),
    .mov .rsi (.mem (ws .rax sOut)), .mov .rcx (.mem (ws .rax sK))]

variable (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) (r2 : Prog isa)

/-- Compute the shared value over every scalar byte, check its range and
write its fixed-width encoding, or zeros for a degenerate value. -/
def main : Prog isa :=
  seqs ([.block head] ++ pSetup ++ [r2] ++ pow mul ex sY sK sX sXl ++ range aY ++
    [.block finBlk, storeBE, .block [.mov .rax (.mem (hdr sF)), leave]])

def body : Prog isa :=
  .seq (.block (entry ++ domHead)) (.ite .ne (ret 0) (main mul ex r2))

/-- Restore the ABI registers after every path. -/
def code : Prog isa := .seq (body mul ex r2) (.block exit)

end VG.Impl.Ffdh.X86_64.Domain.Exchange
