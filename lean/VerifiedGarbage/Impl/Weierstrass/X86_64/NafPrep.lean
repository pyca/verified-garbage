module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Jacobian

/-! Signed five-bit NAF recoding of a public scalar of `n` words into `64 n + 1` bytes. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Naf
open VG VG.X86_64 VG.Impl.Mont.X86_64

/-- The scalar's `n` words and a top word: `r8` up, then `rbp` and `rsi` for
nine words (free while recoding: the prologue saves `rbp`, and `rsi`'s
argument is read by then). -/
def sregs (n : Nat) : List Reg := [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi].take (n+1)

/-- The scalar's top word. -/
def stop (n : Nat) : Reg := (sregs n).getLastD .r8

def initN (n src : Nat) : List Instr :=
  loads ((sregs n).take n) src ++ [.mov32 (stop n) (.imm 0),.mov32 .rbx (.imm 0)]

def init (src : Nat) : List Instr :=
  loads [.r8,.r9,.r10,.r11] src ++ [.mov32 .r12 (.imm 0),.mov32 .rbx (.imm 0)]

def oddDigit : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm 31),.alu .cmp .rcx (.imm 16)])
    (.ite .b (.block []) (.block [.alu .sub .rcx (.imm 32)]))

def subtractDigit : List Instr :=
  [.mov .rax (.reg .rcx),.shift .shr .rax 63,.mov32 .rdx (.imm 0),.alu .sub .rdx (.reg .rax),
   .alu .sub .r8 (.reg .rcx),.alu .sbb .r9 (.reg .rdx),.alu .sbb .r10 (.reg .rdx),
   .alu .sbb .r11 (.reg .rdx),.alu .sbb .r12 (.reg .rdx)]

/-- `r8 … = r8 … - rcx` for the sign-extended digit `rcx`, through `rax` and `rdx`. -/
def subtractDigitN (n : Nat) : List Instr :=
  [.mov .rax (.reg .rcx),.shift .shr .rax 63,.mov32 .rdx (.imm 0),.alu .sub .rdx (.reg .rax),
   .alu .sub .r8 (.reg .rcx)] ++ (sregs n).tail.map fun r => .alu .sbb r (.reg .rdx)

def adjust : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm 1),.alu .test .rcx (.reg .rcx)])
    (.ite .e (.block []) (.seq oddDigit (.block subtractDigit)))

def shift : List Instr :=
  [.shift .shr .r8 1,.mov .rax (.reg .r9),.shift .shl .rax 63,.alu .or .r8 (.reg .rax),
   .shift .shr .r9 1,.mov .rax (.reg .r10),.shift .shl .rax 63,.alu .or .r9 (.reg .rax),
   .shift .shr .r10 1,.mov .rax (.reg .r11),.shift .shl .rax 63,.alu .or .r10 (.reg .rax),
   .shift .shr .r11 1,.mov .rax (.reg .r12),.shift .shl .rax 63,.alu .or .r11 (.reg .rax),
   .shift .shr .r12 1]

def step (dst : Nat) : Prog isa :=
  .seq adjust (.block (([.store8 (tbl dst) .rcx] : List Instr) ++ shift ++
    [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 257)]))

def prep (dst src : Nat) : Prog isa := .seq (.block (init src)) (.loop (step dst) .b)
end VG.Impl.Weierstrass.X86_64.Naf
