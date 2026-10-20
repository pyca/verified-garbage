module
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase


/-! Public width-five recoding into byte digits in unused verification scratch. -/

@[expose] public section

namespace VG.Impl.Ed448.X86_64.Wnaf
open VG.X86_64

def SDIG : Nat := 3072
def KDIG : Nat := 3536

/-- Read five expanded bits, leaving the low bit in `rdx`. -/
def loadBits (o : Nat) : List Instr :=
  [.movzx8 .rax { base := .rdi, index := some .rbx, disp := ((o + 4 : Nat) : Int) }] ++
  [3, 2, 1, 0].flatMap fun i =>
    [.movzx8 .rdx { base := .rdi, index := some .rbx, disp := ((o + i : Nat) : Int) },
     .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx)]

/-- `rax` is the lookahead, `rdx` its low bit, `rcx` the carry biased by 16.
Return the signed digit in `r15` and the next biased carry in `rcx`. -/
def digitStep : List Instr :=
  [.alu .add .rax (.reg .rcx), .alu .add .rax (.imm 16), .alu .and .rax (.imm 31),
   .mov .r15 (.reg .rax), .alu .sub .r15 (.imm 32), .alu .cmp .rax (.imm 16),
   .cmov .b .r15 (.reg .rax), .alu .test .rax (.imm 1), .mov32 .rax (.imm 0),
   .cmov .e .r15 (.reg .rax),
   .alu .add .rcx (.reg .rdx), .alu .add .rcx (.imm 16), .alu .sub .rcx (.reg .r15),
   .shift .shr .rcx 1]

def writeDigit (o : Nat) : List Instr :=
  [.store8 { base := .rdi, index := some .rbx, disp := (o : Int) } .r15,
   .alu .add .rbx (.imm 1)]

def recodeStep (src dst : Nat) : List Instr :=
  loadBits src ++ digitStep ++ writeDigit dst ++ [.alu .cmp .rbx (.imm 456)]

def zeroStep (dst : Nat) : List Instr :=
  [.mov32 .rax (.imm 0), .mov32 .rdx (.imm 0)] ++ digitStep ++ writeDigit dst

def recodeTail (dst : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (zeroStep dst)) (recodeTail dst n)

/-- Input padding suffices for the first 456 positions; the five carry positions
have zero input bits and do not read beyond that padding. -/
def recode (src dst : Nat) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0), .mov32 .rcx (.imm 16)]) <|
  .seq (.loop (.block (recodeStep src dst)) .ne) <|
  recodeTail dst 5

end VG.Impl.Ed448.X86_64.Wnaf
