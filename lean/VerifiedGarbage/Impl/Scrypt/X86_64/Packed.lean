module

public import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix

/-! SSE2 BlockMix. Four packed vectors retain the complete Salsa state
between blocks. GPRs retain input/output pointers and the public loop count.
No scalar/SIMD conversion or state spill occurs between Salsa invocations. -/

@[expose] public section
namespace VG.Impl.Scrypt.X86_64.Packed
open VG.X86_64

def row : Nat → XReg | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | _ => .xmm3

def index (r q : Nat) : Nat := (4*r + 5*q) % 16

/-- Transpose four rows in xmm4–7. Outputs: column 0 in xmm12,
column 1 in xmm5, column 2 in xmm4, column 3 in xmm7. -/
def transpose : List XOp := [
 .bin .movdqa .xmm12 .xmm4, .bin .punpckldq .xmm12 .xmm5,
 .bin .punpckhdq .xmm4 .xmm5,
 .bin .movdqa .xmm13 .xmm6, .bin .punpckldq .xmm13 .xmm7,
 .bin .punpckhdq .xmm6 .xmm7,
 .bin .movdqa .xmm5 .xmm12, .bin .punpckhqdq .xmm5 .xmm13,
 .bin .punpcklqdq .xmm12 .xmm13,
 .bin .movdqa .xmm7 .xmm4, .bin .punpckhqdq .xmm7 .xmm6,
 .bin .punpcklqdq .xmm4 .xmm6]

/-- Natural rows to the diagonal Salsa layout. Outputs A/B/C/D occupy
xmm12/xmm7/xmm4/xmm5 respectively. -/
def pack : List XOp :=
 [.pshufd .xmm5 .xmm5 0x39, .pshufd .xmm6 .xmm6 0x4e,
  .pshufd .xmm7 .xmm7 0x93] ++ transpose ++
 [.pshufd .xmm7 .xmm7 0x39, .pshufd .xmm4 .xmm4 0x4e,
  .pshufd .xmm5 .xmm5 0x93]

def naturalReg : Nat → XReg | 0 => .xmm4 | 1 => .xmm5 | 2 => .xmm6 | _ => .xmm7

def naturalLoad (src : Reg) (off : Nat) : List Instr :=
 [.movdquLoad .xmm4 (at_ src off), .movdquLoad .xmm5 (at_ src (off+16)),
  .movdquLoad .xmm6 (at_ src (off+32)), .movdquLoad .xmm7 (at_ src (off+48))]

def packedReg : Nat → XReg | 0 => .xmm12 | 1 => .xmm7 | 2 => .xmm4 | _ => .xmm5

def retain : List Instr :=
 (List.range 4).map (fun k => .xop (.bin .movdqa (row k) (packedReg k)))

def load : List Instr := naturalLoad .r15 0 ++ pack.map .xop ++ retain

/-- The four lane-parallel Salsa lines. -/
def line (i j k : XReg) (n : Nat) : List Instr :=
 ([.bin .movdqa .xmm4 k, .bin .movdqa .xmm5 k,
  .bin .paddd .xmm4 j, .bin .paddd .xmm5 j,
  .shift .pslld .xmm4 (BitVec.ofNat 8 n),
  .shift .psrld .xmm5 (BitVec.ofNat 8 (32-n)),
  .bin .por .xmm4 .xmm5, .bin .pxor i .xmm4] : List XOp).map .xop

def quarter (a b c d : XReg) : List Instr :=
 line b a d 7 ++ line c b a 9 ++ line d c b 13 ++ line a d c 18

def toRows : List Instr :=
 ([.pshufd .xmm3 .xmm3 0x39, .pshufd .xmm1 .xmm1 0x93,
  .pshufd .xmm2 .xmm2 0x4e] : List XOp).map .xop

def toCols : List Instr :=
 ([.pshufd .xmm3 .xmm3 0x93, .pshufd .xmm1 .xmm1 0x39,
  .pshufd .xmm2 .xmm2 0x4e] : List XOp).map .xop

/-- Changing register names exchanges B and D without a move instruction. -/
def doubleRound : List Instr :=
 quarter .xmm0 .xmm1 .xmm2 .xmm3 ++ toRows ++
 quarter .xmm0 .xmm3 .xmm2 .xmm1 ++ toCols

def rounds : Nat → Prog isa
 | 0 => .block []
 | n+1 => .seq (rounds n) (.block doubleRound)

/-- Copy the retained state and invert pack, without modifying xmm0–3.
Natural output rows occupy xmm12/xmm5/xmm4/xmm7. -/
def unpack : List XOp :=
 [.bin .movdqa .xmm4 .xmm0, .pshufd .xmm5 .xmm3 0x39,
  .pshufd .xmm6 .xmm2 0x4e, .pshufd .xmm7 .xmm1 0x93] ++ transpose ++
 [.pshufd .xmm5 .xmm5 0x93, .pshufd .xmm4 .xmm4 0x4e,
  .pshufd .xmm7 .xmm7 0x39]

def outputReg : Nat → XReg | 0 => .xmm12 | 1 => .xmm5 | 2 => .xmm4 | _ => .xmm7

def store (dst : Reg) : List Instr := unpack.map .xop ++
 (List.range 4).map (fun k => .movdquStore (at_ dst (16*k)) (outputReg k))

def savedInput : Nat → XReg | 0 => .xmm8 | 1 => .xmm9 | 2 => .xmm10 | _ => .xmm11

def xorState : List Instr :=
 (List.range 4).map (fun k => .xop (.bin .pxor (row k) (packedReg k)))

def saveInput : List Instr :=
 (List.range 4).map (fun k => .xop (.bin .movdqa (savedInput k) (row k)))

def absorb (off : Nat) : List Instr :=
 naturalLoad .rbx off ++ pack.map .xop ++ xorState ++ saveInput

def finish : List Instr :=
 (List.range 4).map (fun k => .xop (.bin .paddd (row k) (savedInput k)))

def half (off : Nat) (dst : Reg) : Prog isa :=
 .seq (.block (absorb off)) (.seq (rounds 4) (.block (finish ++ store dst)))

def tail : List Instr :=
 [.mov .r15 (.reg .r12), .alu .add .rbx (.imm 128), .alu .add .rbp (.imm 64),
  .alu .add .r12 (.imm 64), .alu .sub .r14 (.imm 1)]

def body : Prog isa := .seq (half 0 .rbp) (.seq (half 64 .r12) (.block tail))

def blockMix : Prog isa :=
 .seq (.block (bmPrologue ++ load)) (.seq (.loop body .ne) (.block bmEpilogue))

end VG.Impl.Scrypt.X86_64.Packed
