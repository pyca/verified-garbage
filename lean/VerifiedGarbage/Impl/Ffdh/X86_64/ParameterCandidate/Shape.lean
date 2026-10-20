module
public import VerifiedGarbage.Impl.Bignum.X86_64


/-! # FFDH parameter candidates on x86-64: shape p and halve it for q -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- Select the low-byte mask and highest bit for an index in 0..7. -/
def maskCase (j : Nat) : List Instr :=
  [.alu .cmp .rdx (.imm (BitVec.ofNat 32 j)),
    .mov32 .r10 (.imm (BitVec.ofNat 32 (2 ^ j - 1))), .cmov .e .r8 (.reg .r10),
    .mov32 .r10 (.imm (BitVec.ofNat 32 (2 ^ j))), .cmov .e .r9 (.reg .r10)]

/-- The last index is the default. Only the public residual bit count is tested. -/
def maskLookup : List Instr :=
  [.mov32 .r8 (.imm 127), .mov32 .r9 (.imm 128)] ++ (List.range 7).flatMap maskCase

/-- Copy an octet after the first, preserving its bits. -/
def copyByte : List Instr :=
  [.movzx8 .rax (at0 .r10), .store8 (at0 .r11) .rax,
    .alu .add .r10 (.imm 1), .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]

def shapeMasks : List Instr := [.alu .sub .rdx (.imm 1), .alu .and .rdx (.imm 7)] ++ maskLookup

def firstByte : List Instr :=
  [.mov .r10 (.reg .rsi), .mov .r11 (.reg .rdi), .movzx8 .rax (at0 .r10),
    .alu .and .rax (.reg .r8), .alu .or .rax (.reg .r9), .store8 (at0 .r11) .rax,
    .alu .add .r10 (.imm 1), .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]

def setLow : List Instr :=
  [.movzx8 .rax { base := .r11, disp := -1 }, .alu .or .rax (.imm 1), .store8 { base := .r11, disp := -1 } .rax]

/-- `(out = rdi, rand = rsi, len = rcx, bits = rdx)`: copy, cut the high
byte, and set the candidate's highest and lowest bits. len is at least 2. -/
def shape : Prog isa := seqs [
  .block shapeMasks, .block firstByte, .loop (.block copyByte) .ne, .block setLow]

/-- Right-shift one big-endian byte with its carry from the preceding byte. -/
def halveByte : List Instr :=
  [.movzx8 .rax (at0 .r10), .mov .rdx (.reg .rax), .shift .shr .rax 1,
    .alu .or .rax (.reg .r8), .store8 (at0 .r10) .rax, .alu .and .rdx (.imm 1),
    .shift .shl .rdx 7, .mov .r8 (.reg .rdx), .alu .add .r10 (.imm 1), .alu .sub .rcx (.imm 1)]

/-- `(out = rdi, len = rcx)`: replace p's encoding with floor(p/2), which
is (p-1)/2 for an odd candidate. -/
def halve : Prog isa := .seq
  (.block [.mov .r10 (.reg .rdi), .mov32 .r8 (.imm 0)]) (.loop (.block halveByte) .ne)

end VG.Impl.Ffdh.X86_64.ParameterCandidate
