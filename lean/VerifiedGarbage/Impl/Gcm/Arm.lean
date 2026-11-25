module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# GHASH on ARMv7, with integer multiplications

`vg_ghash(h = r0, y = r1, data = r2, n = r3, scratch)`, `scratch` on the
stack.

A block is four byte-reversed words, `y₃` (its first 4 bytes) to `y₀`. The
key is used as `H · x⁻¹`, which makes up for the factor `x` of carry-less
products of words read in this order.

* The carry-less product of two 16-bit words is the sum of nine integer
  products (`prod`), of which only the low 32 bits are needed: each word is
  split into the three classes of its bit positions modulo 3. The partial
  products of class `i` by class `j` lie at positions of class `i + j`, at
  most 6 at each, which is less than 2³, so that a position's sum does not
  carry into the next of its class. The three products that meet in a class
  are added with XOR and masked once.
* Karatsuba's method, three times, multiplies two blocks with 27 of them.
* The product is reduced with shifted operands: `x¹²⁸ = 1 + x + x² + x⁷`.

`scratch` (its address in `r12`) holds the key's 27 halves, the nine words
multiplied, the 12 words of the products, the callee-saved registers, the
pointers and the count. Every branch and every address depends only on the
pointers and `n`.
-/

@[expose] public section

namespace VG.Impl.Gcm.Arm

open VG.Arm

def eor (d n m : Reg) : Instr := .dp .eor d n (.reg m)
def lslI (d m : Reg) (k : Nat) : Instr := .mov d (.shifted m .lsl k)
def lsrI (d m : Reg) (k : Nat) : Instr := .mov d (.shifted m .lsr k)

/-- Word `k` of `scratch`. -/
def ld (d : Reg) (k : Nat) : Instr := .ldr d .r12 (4 * k)
def st (d : Reg) (k : Nat) : Instr := .str d .r12 (4 * k)

/-- The positions congruent to `r` modulo 3. -/
def mask (r : Nat) : BitVec 32 :=
  match r with
  | 0 => 0x49249249#32 | 1 => 0x92492492#32 | _ => 0x24924924#32

def maskReg (r : Nat) : Reg :=
  match r with
  | 0 => .r1 | 1 => .r2 | _ => .r3

def setMask (r : Nat) : List Instr :=
  [.movw (maskReg r) ((mask r).extractLsb' 0 16), .movt (maskReg r) ((mask r).extractLsb' 16 16)]

/-! ## The words of `scratch` -/

/-- The words multiplied, `y₀` and `y₁`, their sum, `y₂` and `y₃`, their sum,
and the sums of the first two and of the last two, and theirs. -/
def opS : Nat := 27
def y0S : Nat := 27
def y1S : Nat := 28
def y2S : Nat := 30
def y3S : Nat := 31
/-- The products, of the low words, the high ones and the sums. -/
def lS : Nat := 36
def hS : Nat := 40
def cS : Nat := 44
def t0S : Nat := 48
def t1S : Nat := 49
def ypS : Nat := 59
def dpS : Nat := 60
def nS : Nat := 61

def saved : List (Reg × Nat) :=
  [(.r4, 50), (.r5, 51), (.r6, 52), (.r7, 53), (.r8, 54), (.r9, 55), (.r10, 56), (.r11, 57), (.lr, 58)]

def save : List Instr := saved.map fun p => st p.1 p.2
def restore : List Instr := saved.map fun p => ld p.1 p.2

/-! ## The key -/

/-- `d ^= s ≪ 31 ^ s ≪ 30 ^ s ≪ 25`. -/
def foldDn (d s : Reg) : List Instr :=
  [.dp .eor d d (.shifted s .lsl 31), .dp .eor d d (.shifted s .lsl 30), .dp .eor d d (.shifted s .lsl 25)]

/-- `d ^= s ≫ 1 ^ s ≫ 2 ^ s ≫ 7`. -/
def foldUp (d s : Reg) : List Instr :=
  [.dp .eor d d (.shifted s .lsr 1), .dp .eor d d (.shifted s .lsr 2), .dp .eor d d (.shifted s .lsr 7)]

def loadBlk (b : Reg) : List Instr := [.ldr .r4 b 0, .ldr .r5 b 4, .ldr .r6 b 8, .ldr .r7 b 12]
def revBlk : List Instr := [.rev .r4 .r4, .rev .r5 .r5, .rev .r6 .r6, .rev .r7 .r7]

/-- `H · x⁻¹`, from `H`'s words in `r4`–`r7`, the first in `r4`. -/
def adjust : List Instr :=
  ([lsrI .r8 .r4 31,
    lslI .r4 .r4 1, .dp .eor .r4 .r4 (.shifted .r5 .lsr 31),
    lslI .r5 .r5 1, .dp .eor .r5 .r5 (.shifted .r6 .lsr 31),
    lslI .r6 .r6 1, .dp .eor .r6 .r6 (.shifted .r7 .lsr 31),
    lslI .r7 .r7 1, .dp .eor .r7 .r7 (.reg .r8)] : List Instr) ++ foldDn .r4 .r8

/-- The halves of the word in `r` and their sum. -/
def keyWord (t : Nat) (r : Reg) : List Instr :=
  [lslI .r9 r 16, lsrI .r9 .r9 16, st .r9 (3 * t), lsrI .r10 r 16, st .r10 (3 * t + 1), eor .r9 .r9 .r10,
   st .r9 (3 * t + 2)]

def keySum (d n m : Reg) : List Instr := [eor d n m]

def keyCode : List Instr :=
  adjust ++ keyWord 0 .r7 ++ keyWord 1 .r6 ++ keySum .r8 .r7 .r6 ++ keyWord 2 .r8 ++
  keyWord 3 .r5 ++ keyWord 4 .r4 ++ keySum .r8 .r5 .r4 ++ keyWord 5 .r8 ++
  keySum .r7 .r7 .r5 ++ keyWord 6 .r7 ++ keySum .r6 .r6 .r4 ++ keyWord 7 .r6 ++ keySum .r8 .r7 .r6 ++ keyWord 8 .r8

/-! ## The product of two 16-bit words -/

/-- The classes of the key's word. -/
def kc (i : Nat) : Reg :=
  match i with
  | 0 => .r7 | 1 => .r8 | _ => .r9

/-- The class `r` of the product. -/
def classSum (q : Reg) (r : Nat) : List Instr :=
  [.mul q .r4 (kc (r % 3)), .mul .r11 .r5 (kc ((r + 2) % 3)), eor q q .r11,
   .mul .r11 .r6 (kc ((r + 1) % 3)), eor q q .r11, .dp .and q q (.reg (maskReg r))]

/-- The classes of the high half of `x` and of the key's half `j`. -/
def classes (x : Reg) (j : Nat) : List Instr :=
  [.dp .and .r4 .r1 (.shifted x .lsr 16), .dp .and .r5 .r2 (.shifted x .lsr 16), .dp .and .r6 .r3 (.shifted x .lsr 16),
   ld .r11 j, .dp .and .r7 .r11 (.reg .r1), .dp .and .r8 .r11 (.reg .r2), .dp .and .r9 .r11 (.reg .r3)]

/-- The product of the high half of `x` and the key's half `j`, in `r0`. -/
def prod (x : Reg) (j : Nat) : List Instr :=
  classes x j ++ classSum .r0 0 ++ classSum .r10 1 ++ ([eor .r0 .r0 .r10] : List Instr) ++ classSum .r10 2 ++
  ([eor .r0 .r0 .r10] : List Instr)

/-- The product of word `k` and the key's word `t`, in `r5 : r4`. -/
def mul32 (k t : Nat) : List Instr :=
  ([ld .lr k, lslI .r11 .lr 16] : List Instr) ++ prod .r11 (3 * t) ++ ([st .r0 t0S] : List Instr) ++
  prod .lr (3 * t + 1) ++ ([st .r0 t1S, .dp .eor .r11 .lr (.shifted .lr .lsl 16)] : List Instr) ++
  prod .r11 (3 * t + 2) ++
  ([ld .r4 t0S, ld .r5 t1S, eor .r0 .r0 .r4, eor .r0 .r0 .r5, .dp .eor .r4 .r4 (.shifted .r0 .lsl 16),
    .dp .eor .r5 .r5 (.shifted .r0 .lsr 16)] : List Instr)

def keep (b : Nat) : List Instr := [st .r4 b, st .r5 (b + 1)]

/-- The product of words `t` and `t + 1` and the key's, at `b`. -/
def mul64 (t b : Nat) : List Instr :=
  mul32 (opS + t) t ++ keep b ++ mul32 (opS + (t + 1)) (t + 1) ++ keep (b + 2) ++ mul32 (opS + (t + 2)) (t + 2) ++
  ([ld .r6 b, ld .r7 (b + 1), ld .r8 (b + 2), ld .r9 (b + 3),
    eor .r4 .r4 .r6, eor .r4 .r4 .r8, eor .r5 .r5 .r7, eor .r5 .r5 .r9,
    eor .r7 .r7 .r4, eor .r8 .r8 .r5, st .r7 (b + 1), st .r8 (b + 2)] : List Instr)

/-! ## A block -/

def loadX : List Instr :=
  ([ld .r11 dpS] : List Instr) ++ loadBlk .r11 ++ ([.dp .add .r11 .r11 (.imm 16), st .r11 dpS] : List Instr)

/-- The block in `r4`–`r7` added to `Y`, and the words multiplied. -/
def addX : List Instr :=
  revBlk ++
  ([ld .r8 y3S, eor .r4 .r4 .r8, ld .r8 y2S, eor .r5 .r5 .r8, ld .r8 y1S, eor .r6 .r6 .r8, ld .r8 y0S, eor .r7 .r7 .r8,
    st .r4 y3S, st .r5 y2S, st .r6 y1S, st .r7 y0S,
    eor .r8 .r7 .r6, st .r8 (opS + 2), eor .r8 .r5 .r4, st .r8 (opS + 5), eor .r8 .r7 .r5, st .r8 (opS + 6),
    eor .r9 .r6 .r4, st .r9 (opS + 7), eor .r8 .r8 .r9, st .r8 (opS + 8)] : List Instr)

/-- The products reduced. -/
def reduce : List Instr :=
  ([ld .r4 lS, ld .r5 (lS + 1), ld .r6 (lS + 2), ld .r7 (lS + 3), ld .r8 hS, ld .r9 (hS + 1),
    ld .r10 cS, eor .r10 .r10 .r4, eor .r10 .r10 .r8, eor .r10 .r10 .r6,
    ld .r11 (cS + 1), eor .r11 .r11 .r5, eor .r11 .r11 .r9, eor .r11 .r11 .r7] : List Instr) ++ foldDn .r11 .r4 ++
  ([ld .r0 (cS + 2), eor .r0 .r0 .r6, ld .lr (hS + 2), eor .r0 .r0 .lr, eor .r8 .r8 .r0, eor .r8 .r8 .r4] : List Instr) ++
  foldUp .r8 .r4 ++ foldDn .r8 .r5 ++
  ([ld .r6 (cS + 3), eor .r6 .r6 .r7, ld .r7 (hS + 3), eor .r6 .r6 .r7, eor .r9 .r9 .r6, eor .r9 .r9 .r5] : List Instr) ++
  foldUp .r9 .r5 ++ foldDn .r9 .r10 ++ ([eor .lr .lr .r10] : List Instr) ++ foldUp .lr .r10 ++ foldDn .lr .r11 ++
  ([eor .r7 .r7 .r11] : List Instr) ++ foldUp .r7 .r11 ++
  ([st .r8 y0S, st .r9 y1S, st .lr y2S, st .r7 y3S] : List Instr)

def next : List Instr := [ld .r4 nS, .dp .sub .r4 .r4 (.imm 1), st .r4 nS]

def body : List Instr :=
  loadX ++ addX ++ mul64 0 lS ++ mul64 3 hS ++ mul64 6 cS ++ reduce ++ next ++ ([.cmp .r4 (.imm 0)] : List Instr)

def storeYs : List Instr := [st .r4 y3S, st .r5 y2S, st .r6 y1S, st .r7 y0S]

def prologue : List Instr :=
  ([.ldrSp .r12 0] : List Instr) ++ save ++ ([st .r1 ypS, st .r2 dpS, st .r3 nS] : List Instr) ++ loadBlk .r0 ++ revBlk ++
  keyCode ++ loadBlk .r1 ++ revBlk ++ storeYs ++ setMask 0 ++ setMask 1 ++ setMask 2 ++
  ([ld .r4 nS, .cmp .r4 (.imm 0)] : List Instr)

def epilogue : List Instr :=
  ([ld .r0 y3S, ld .r1 y2S, ld .r2 y1S, ld .r3 y0S, .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3] : List Instr) ++
  restore ++ ([ld .r12 ypS, .str .r0 .r12 0, .str .r1 .r12 4, .str .r2 .r12 8, .str .r3 .r12 12] : List Instr)

def ghash : Prog isa :=
  .seq (.block prologue) (.seq (.ite .eq (.block []) (.loop (.block body) .ne)) (.block epilogue))

end VG.Impl.Gcm.Arm
