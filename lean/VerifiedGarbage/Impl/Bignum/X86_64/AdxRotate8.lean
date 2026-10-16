module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxDualAdd

/-! Eight register-resident columns of a multiply-add, shifted by one word. -/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.AdxRotate8
open VG.X86_64 VG.Impl.Bignum.X86_64

def at_ (r : Reg) (d : Nat) : MemOp := { base := r, disp := (d : Int) }

/-- Consume one modulus word while rotating its high product into a column. -/
def word (k : Nat) (hi prev next : Reg) : List Instr :=
  [.mulx hi .rax (.mem (at_ .rbp (8 * k))), .adcx prev (.reg .rax), .adox hi (.reg next)]

/-- Close both carry chains using the now-dead low-product register. -/
def close : List Instr :=
  [.mov32 .rax (.imm 0), .adox .r15 (.reg .rax), .adcx .r15 (.reg .rax)]

/-- Low word to `rbx`, quotient to `r8` through `r15`. No memory is written. -/
def core : List Instr :=
  ([.mov .rbx (.reg .r8), .alu32 .xor .rax (.reg .rax)] : List Instr) ++
  word 0 .r8 .rbx .r9 ++ word 1 .r9 .r8 .r10 ++
  word 2 .r10 .r9 .r11 ++ word 3 .r11 .r10 .r12 ++
  word 4 .r12 .r11 .r13 ++ word 5 .r13 .r12 .r14 ++
  word 6 .r14 .r13 .r15 ++
  ([.mulx .r15 .rax (.mem (at_ .rbp 56)), .adcx .r14 (.reg .rax)] : List Instr) ++ close
/-- Load the next eight accumulator words. -/
def loadCols : List Instr :=
  [.mov .r8 (.mem (at_ .rsi 0)), .mov .r9 (.mem (at_ .rsi 8)), .mov .r10 (.mem (at_ .rsi 16)), .mov .r11 (.mem (at_ .rsi 24)), .mov .r12 (.mem (at_ .rsi 32)), .mov .r13 (.mem (at_ .rsi 40)), .mov .r14 (.mem (at_ .rsi 48)), .mov .r15 (.mem (at_ .rsi 56))]

/-- Store the eight accumulator words. -/
def storeCols : List Instr :=
  [.store (at_ .rsi 0) .r8, .store (at_ .rsi 8) .r9, .store (at_ .rsi 16) .r10, .store (at_ .rsi 24) .r11, .store (at_ .rsi 32) .r12, .store (at_ .rsi 40) .r13, .store (at_ .rsi 48) .r14, .store (at_ .rsi 56) .r15]

/-- `[b + i + d]`, for a byte index `i`. -/
def atx (b i : Reg) (d : Nat) : MemOp := { base := b, index := some i, disp := (d : Int) }

/-- The steps in each iteration of the tile's loops, which count a byte index
from `-64` up to `0`: unrolled code would not fit some CPUs' decoded-µop caches. -/
def unroll : Nat := 4

/-- Cancel one word and retain its multiplier at `m` for the remaining blocks. -/
def digit (m : MemOp) : List Instr :=
  [.mov .rdx (.reg .r8), .mulx .rax .rdx (.mem (hdr sMinv)), .store m .rdx]

/-- The cancellation `j` words into an iteration, its digit `rsi` bytes past `rcx + 64`. -/
def headStep (j : Nat) : Prog isa := .seq (.block (digit (atx .rcx .rsi (64 + 8 * j)))) (.block core)

def headSteps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (headSteps n) (headStep n)

/-- The low eight modulus words determine eight cancellation digits, `unroll`
per iteration, indexed by `rsi`, which ends as `rcx`. -/
def headLoop : Prog isa :=
  .seq (.block [.mov .rsi (.imm (-64))])
    (.seq (.loop (.seq (headSteps unroll) (.block [.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * unroll)))])) .ne)
      (.block [.mov .rsi (.reg .rcx)]))

def addChain (src : Nat → Src) : List Instr :=
  [.adcx .r8 (src 0), .adcx .r9 (src 1), .adcx .r10 (src 2), .adcx .r11 (src 3), .adcx .r12 (src 4), .adcx .r13 (src 5), .adcx .r14 (src 6), .adcx .r15 (src 7)]

/-- Add the next input block, retaining overflow in `rax`. -/
def addMem : List Instr :=
  ([.alu32 .xor .rax (.reg .rax)] : List Instr) ++ addChain (fun k => .mem (at_ .rsi (8 * k))) ++
  ([.adcx .rax (.reg .rax)] : List Instr)

/-- Add a word to the columns, accumulating its overflow in `rax`.
The incoming CF is clear and `rax` is a small carry count. -/
def addWord (src : MemOp) : List Instr :=
  ([.mov32 .rdx (.imm 0)] : List Instr) ++ addChain (fun k => if k = 0 then .mem src else .reg .rdx) ++
  ([.adcx .rax (.reg .rdx)] : List Instr)

def blockCarry : MemOp := { base := .rcx, disp := -8 }
def tileCarry : MemOp := { base := .rcx, disp := -16 }

/-- The product with the digit `j` words into an iteration: digit and output
`rdi` bytes past `rcx + 64` and `rsi + 64`. -/
def productStep (j : Nat) : Prog isa :=
  .seq (.block [.mov .rdx (.mem (atx .rcx .rdi (64 + 8 * j)))])
    (.seq (.block core) (.block [.store (atx .rsi .rdi (64 + 8 * j)) .rbx]))

def productSteps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (productSteps n) (productStep n)

/-- A modulus block times the eight digits, `unroll` steps per iteration, indexed by `rdi`: the header
base waits in `xmm0`. -/
def productLoop : Prog isa :=
  .seq (.block [.xop (.movq .xmm0 .rdi), .mov .rdi (.imm (-64))])
    (.seq (.loop (.seq (productSteps unroll) (.block [.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * unroll)))])) .ne)
      (.block [.movqR .rdi .xmm0]))

/-- Advance both public block pointers and test the modulus endpoint. -/
def nextBlock : List Instr :=
  [.alu .add .rbp (.imm 64), .alu .add .rsi (.imm 64),
    .mov .rax (.mem (hdr sW)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.mem (hdr (sArr Public.aN))), .alu .cmp .rbp (.reg .rax)]

def addInputCarry : List Instr := ([.mov .rdx (.mem blockCarry)] : List Instr) ++ AdxDualAdd.addInput

def accumulate : Prog isa :=
  .seq (.block addInputCarry) (.block [.store blockCarry .rax])

def middleBody : Prog isa := .seq accumulate productLoop

def middle : Prog isa := .seq middleBody (.block nextBlock)

def tileBegin : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rcx), .mov .rbp (.mem (hdr (sArr Public.aN)))]) (.block loadCols)

def clearCarry : List Instr := [.mov32 .rax (.imm 0), .store blockCarry .rax]

def tailCore : Prog isa :=
  .seq (.block addInputCarry) (.seq (.block (addWord tileCarry)) (.block storeCols))

def tileEnd : List Instr :=
  [.store (at_ .rcx 48) .rax, .alu .add .rcx (.imm 64),
    .alu .cmp .rcx (.mem (hdr (sArr Public.aTmp)))]

def tileFront : Prog isa :=
  .seq tileBegin (.seq headLoop (.seq (.block clearCarry) (.block nextBlock)))

def tileCompute : Prog isa :=
  .seq tileFront (.seq (.ite .ne (.loop middle .ne) (.block [])) tailCore)

/-- One eight-word cancellation tile. Carries occupy discarded words below
its digit table, within the existing accumulator arrays. -/
def tile : Prog isa :=
  .seq tileCompute (.block tileEnd)

def setupBases : List Instr :=
  [.mov .rcx (.mem (hdr (sArr Public.aAcc))), .alu .add .rcx (.imm 16)]

def setup : List Instr := setupBases ++ ([.mov32 .rax (.imm 0), .store tileCarry .rax] : List Instr)

def finishSetup : List Instr :=
  [.mov .r8 (.reg .rcx), .mov .rbp (.mem (hdr sW)), .mov .r10 (.mem tileCarry)]

def finish : List Instr := finishSetup ++
  ([.store (ix .r8 .rbp) .r10, .mov32 .rax (.imm 0), .store (ix .r8 .rbp 8) .rax] : List Instr)

/-- Register-tiled Montgomery reduction for a positive multiple of eight words. -/
def redc : Prog isa := .seq (.block setup) (.seq (.loop tile .ne) (.block finish))
end VG.Impl.Bignum.X86_64.AdxRotate8
