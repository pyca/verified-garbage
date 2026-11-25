module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# GHASH on x86 (32-bit), with integer multiplications

`vg_ghash(h, y, data, n, scratch)`, in the baseline ISA. It uses no stack.

A block is four byte-reversed words, `y₃` (its first 4 bytes) to `y₀`. The
key is used as `H · x⁻¹`, which makes up for the factor `x` of carry-less
products of words read in this order.

* The carry-less product of two words is the sum of 16 integer products of 64
  bits (`mul32`): each word is split into the four classes of its bit
  positions modulo 4. The partial products of class `i` by class `j` lie at
  positions of class `i + j`, at most 8 at each, which is less than 2⁴, so
  that a position's sum does not carry into the next of its class. The four
  products that meet in a class are added with XOR and masked once.
* Karatsuba's method, twice, multiplies two blocks with nine of them.
* The product is reduced with shifts and rotations: `x¹²⁸ = 1 + x + x² + x⁷`.

`scratch` (its address in `ecx`) holds the key's nine words in their four
classes, the classes of the word being multiplied, `Y`, the 12 words of the
products, the callee-saved registers, the data pointer and the count. Every
branch and every address depends only on the pointers and `n`.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- Word `k` of `scratch`. -/
def slot (k : Nat) : MemOp := at_ .ecx (4 * k)
def ld (d : Reg) (k : Nat) : Instr := .mov d (.mem (slot k))
def st (k : Nat) (r : Reg) : Instr := .store (slot k) r
def xorR (d r : Reg) : Instr := .alu .xor d (.reg r)
def xorM (d : Reg) (k : Nat) : Instr := .alu .xor d (.mem (slot k))
def mv (d r : Reg) : Instr := .mov d (.reg r)
def shr (d : Reg) (n : Nat) : Instr := .shift .shr d n
def ror (d : Reg) (n : Nat) : Instr := .shift .ror d n

/-- The positions congruent to `j` modulo 4. -/
def mask (j : Nat) : BitVec 32 := 0x11111111#32 <<< j

/-! ## The words of `scratch`: the key's first -/

/-- The classes of the word being multiplied. -/
def wS : Nat := 36
/-- `y₀` to `y₃`. -/
def yS : Nat := 40
/-- The products, of the low words, the high ones and the sums. -/
def lS : Nat := 44
def hS : Nat := 48
def cS : Nat := 52
def dpS : Nat := 60
def nS : Nat := 61

def saved : List (Reg × Nat) := [(.ebx, 56), (.esi, 57), (.edi, 58), (.ebp, 59)]
def save : List Instr := saved.map fun p => st p.2 p.1
def restore : List Instr := saved.map fun p => ld p.1 p.2

/-! ## The key -/

/-- A block, its first word in `eax`. -/
def loadBlk : List Instr :=
  [.mov .eax (.mem (at_ .edx 0)), .mov .ebx (.mem (at_ .edx 4)), .mov .esi (.mem (at_ .edx 8)),
   .mov .edi (.mem (at_ .edx 12))]

def revBlk : List Instr := [.bswap .eax, .bswap .ebx, .bswap .esi, .bswap .edi]

/-- `H · x⁻¹`, from `H`'s words in `eax`, `ebx`, `esi` and `edi`. -/
def adjust : List Instr :=
  [mv .ebp .eax, shr .ebp 31,
   .alu .add .eax (.reg .eax), mv .edx .ebx, shr .edx 31, xorR .eax .edx,
   .alu .add .ebx (.reg .ebx), mv .edx .esi, shr .edx 31, xorR .ebx .edx,
   .alu .add .esi (.reg .esi), mv .edx .edi, shr .edx 31, xorR .esi .edx,
   .alu .add .edi (.reg .edi), xorR .edi .ebp,
   ror .ebp 1, xorR .eax .ebp, ror .ebp 1, xorR .eax .ebp, ror .ebp 5, xorR .eax .ebp]

/-- Class `j` of the word in `r`, at word `b + j`. -/
def classStore (b : Nat) (r : Reg) (j : Nat) : List Instr :=
  [mv .edx r, .alu .and .edx (.imm (mask j)), st (b + j) .edx]

/-- The four classes of the word in `r`, at words `b` to `b + 3`. -/
def split (b : Nat) (r : Reg) : List Instr :=
  classStore b r 0 ++ classStore b r 1 ++ classStore b r 2 ++ classStore b r 3

def keyWord (t : Nat) (r : Reg) : List Instr := split (4 * t) r
def keySum (a b : Reg) : List Instr := [mv .ebp a, xorR .ebp b]

def keyCode : List Instr :=
  adjust ++ keyWord 0 .edi ++ keyWord 1 .esi ++ keySum .edi .esi ++ keyWord 2 .ebp ++
  keyWord 3 .ebx ++ keyWord 4 .eax ++ keySum .ebx .eax ++ keyWord 5 .ebp ++
  keySum .edi .ebx ++ keyWord 6 .ebp ++ ([mv .edi .ebp] : List Instr) ++ keySum .esi .eax ++ keyWord 7 .ebp ++
  ([xorR .ebp .edi] : List Instr) ++ keyWord 8 .ebp

/-! ## The product of two words -/

/-- Class `i` of the word by class `j` of the key's word `t`, in `edx : eax`. -/
def part (t i j : Nat) : List Instr := [ld .eax (wS + i), ld .edx (4 * t + j), .mul .edx]

def addPart : List Instr := [xorR .ebx .eax, xorR .esi .edx]

/-- The class `r` of the product, in `esi : ebx`. -/
def classSum (t r : Nat) : List Instr :=
  part t 0 (r % 4) ++ ([mv .ebx .eax, mv .esi .edx] : List Instr) ++ part t 1 ((r + 3) % 4) ++ addPart ++
  part t 2 ((r + 2) % 4) ++ addPart ++ part t 3 ((r + 1) % 4) ++ addPart ++
  ([.alu .and .ebx (.imm (mask r)), .alu .and .esi (.imm (mask r))] : List Instr)

/-- The word multiplied, the sum of words of `scratch`, in `eax`. -/
def sumWords : List Nat → List Instr
  | [] => []
  | k :: ks => ld .eax k :: ks.map (xorM .eax)

/-- The product of the sum of the words `ks` and the key's word `t`, in
`ebp : edi`. -/
def mul32 (ks : List Nat) (t : Nat) : List Instr :=
  sumWords ks ++ split wS .eax ++ classSum t 0 ++ ([mv .edi .ebx, mv .ebp .esi] : List Instr) ++ classSum t 1 ++
  ([xorR .edi .ebx, xorR .ebp .esi] : List Instr) ++ classSum t 2 ++
  ([xorR .edi .ebx, xorR .ebp .esi] : List Instr) ++ classSum t 3 ++ ([xorR .edi .ebx, xorR .ebp .esi] : List Instr)

def keep (b : Nat) : List Instr := [st b .edi, st (b + 1) .ebp]

/-- The product of two words, the sums of `k₀` and of `k₁`, and the key's words
`t` and `t + 1`, at `b`. -/
def mul64 (k₀ k₁ : List Nat) (t b : Nat) : List Instr :=
  mul32 k₀ t ++ keep b ++ mul32 k₁ (t + 1) ++ keep (b + 2) ++ mul32 (k₀ ++ k₁) (t + 2) ++
  ([ld .eax b, ld .edx (b + 1), ld .ebx (b + 2), ld .esi (b + 3),
    xorR .edi .eax, xorR .edi .ebx, xorR .ebp .edx, xorR .ebp .esi,
    xorR .edx .edi, xorR .ebx .ebp, st (b + 1) .edx, st (b + 2) .ebx] : List Instr)

/-! ## A block -/

def loadX : List Instr :=
  ([ld .edx dpS] : List Instr) ++ loadBlk ++ ([.alu .add .edx (.imm 16), st dpS .edx] : List Instr)

/-- The block added to `Y`. -/
def addX : List Instr :=
  revBlk ++
  ([xorM .eax (yS + 3), xorM .ebx (yS + 2), xorM .esi (yS + 1), xorM .edi yS,
    st (yS + 3) .eax, st (yS + 2) .ebx, st (yS + 1) .esi, st yS .edi] : List Instr)

/-- `eax`'s `≫ 1`, `≫ 2` and `≫ 7`, added, in `esi`, and its `≪ 31`, `≪ 30`
and `≪ 25` in `ebx`: the rotations by 1, 2 and 7 are both. -/
def fold : List Instr :=
  [mv .ebx .eax, shr .ebx 1, mv .esi .ebx, shr .ebx 1, xorR .esi .ebx, shr .ebx 5, xorR .esi .ebx,
   ror .eax 1, mv .ebx .eax, ror .eax 1, xorR .ebx .eax, ror .eax 5, xorR .ebx .eax, xorR .ebx .esi]

/-- The products reduced, at `Y`. -/
def reduce : List Instr :=
  ([ld .eax lS] : List Instr) ++ fold ++
  ([ld .edx (cS + 1), xorM .edx (lS + 1), xorM .edx (hS + 1), xorM .edx (lS + 3), xorR .edx .ebx,
    ld .edi hS, xorM .edi (cS + 2), xorM .edi (lS + 2), xorM .edi (hS + 2), xorM .edi lS, xorR .edi .esi,
    ld .eax (lS + 1)] : List Instr) ++ fold ++
  ([xorR .edi .ebx, st yS .edi,
    ld .edi (hS + 1), xorM .edi (cS + 3), xorM .edi (lS + 3), xorM .edi (hS + 3), xorM .edi (lS + 1), xorR .edi .esi,
    ld .eax cS, xorM .eax lS, xorM .eax hS, xorM .eax (lS + 2), mv .ebp .eax] : List Instr) ++ fold ++
  ([xorR .edi .ebx, st (yS + 1) .edi, ld .edi (hS + 2), xorR .edi .ebp, xorR .edi .esi, mv .eax .edx] : List Instr) ++
  fold ++
  ([xorR .edi .ebx, st (yS + 2) .edi, ld .edi (hS + 3), xorR .edi .edx, xorR .edi .esi, st (yS + 3) .edi] : List Instr)

def next : List Instr := [ld .eax nS, .alu .add .eax (.imm 0xffffffff), st nS .eax]
def test : List Instr := [.alu .test .eax (.reg .eax)]

def body : List Instr :=
  loadX ++ addX ++ mul64 [yS] [yS + 1] 0 lS ++ mul64 [yS + 2] [yS + 3] 3 hS ++
  mul64 [yS, yS + 2] [yS + 1, yS + 3] 6 cS ++ reduce ++ next ++ test

def storeYs : List Instr := [st (yS + 3) .eax, st (yS + 2) .ebx, st (yS + 1) .esi, st yS .edi]

def prologue : List Instr :=
  ([.mov .ecx (.mem (argOp 4))] : List Instr) ++ save ++ ([.mov .edx (.mem (argOp 2))] : List Instr) ++
  ([st dpS .edx] : List Instr) ++ ([.mov .edx (.mem (argOp 3))] : List Instr) ++ ([st nS .edx] : List Instr) ++
  ([.mov .edx (.mem (argOp 0))] : List Instr) ++ loadBlk ++ revBlk ++ keyCode ++
  ([.mov .edx (.mem (argOp 1))] : List Instr) ++ loadBlk ++ revBlk ++ storeYs ++ ([ld .eax nS] : List Instr) ++ test

/-- `Y`'s bytes in order at `yS`, and the registers restored. -/
def finish : List Instr :=
  ([ld .eax (yS + 3), ld .ebx (yS + 2), ld .esi (yS + 1), ld .edi yS] : List Instr) ++ revBlk ++
  ([st yS .eax, st (yS + 1) .ebx, st (yS + 2) .esi, st (yS + 3) .edi] : List Instr) ++ restore

def epilogue : List Instr :=
  finish ++ ([.mov .edx (.mem (argOp 1)), .movdquLoad .xmm0 (slot yS), .movdquStore (at_ .edx 0) .xmm0] : List Instr)

def ghash : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop (.block body) .ne)) (.block epilogue))

end VG.Impl.Gcm.X86
