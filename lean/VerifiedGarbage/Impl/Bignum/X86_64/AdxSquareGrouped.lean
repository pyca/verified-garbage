import VerifiedGarbage.Impl.Bignum.X86_64.Adx

/-! Keep the doubling and diagonal-addition carries live across square words. -/
namespace VG.Impl.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64

def word (dst addend : Reg) : List Instr :=
  [.adcx dst (.reg dst), .adox dst (.reg addend)]

def injectCarry : List Instr :=
  [.alu .add .rcx (.reg .r15), .alu .adc .rax (.imm 0)]

def addPair : List Instr := word .r11 .rcx ++ word .r12 .rax

def initialPair : List Instr :=
  [.mulx .rax .rcx (.reg .rdx)] ++ injectCarry ++
  [.alu32 .xor .rsi (.reg .rsi)] ++ addPair

def pair : List Instr :=
  [.mulx .rax .rcx (.reg .rdx)] ++ word .r11 .rcx ++ word .r12 .rax

def close : List Instr :=
  [.mov32 .r15 (.imm 0), .adcx .r15 (.reg .rsi), .adox .r15 (.reg .rsi)]

def head (k : Nat) : List Instr :=
  [.mov .rdx (.mem (ix .r9 .rbp ((8*k : Nat) : Int))),
   .mov .r11 (.mem (ix .r8 .r14 ((16*k : Nat) : Int))),
   .mov .r12 (.mem (ix .r8 .r14 ((16*k+8 : Nat) : Int)))]

def store (k : Nat) : List Instr :=
  [.store (ix .r8 .r14 ((16*k : Nat) : Int)) .r11, .store (ix .r8 .r14 ((16*k+8 : Nat) : Int)) .r12]

def step (k : Nat) (core : List Instr) : Prog isa :=
  .seq (.block (head k)) (.seq (.block core) (.block (store k)))

def group : Prog isa := seqs [step 0 initialPair, step 1 pair, step 2 pair, step 3 pair,
  .block (close ++ [.alu .add .rbp (.imm 4), .alu .add .r14 (.imm 8), .alu .cmp .rbp (.reg .r10)])]

def diagonal : Prog isa :=
  .seq (.block [.mov32 .r15 (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0)])
    (.loop group .ne)

end VG.Impl.Bignum.X86_64.AdxSquareGrouped
