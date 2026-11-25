module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# GHASH on x86-64, with integer multiplications

`vg_ghash(h = rdi, y = rsi, data = rdx, n = rcx, scratch = r8)`, in the
baseline ISA.

A block is two byte-reversed words, `y₁` (its first 8 bytes) and `y₀`, whose
bit `63 − i` is the coefficient of `xⁱ` (and of `x⁶⁴⁺ⁱ`). The key is used as
`H · x⁻¹`, which makes up for the factor `x` of carry-less products of words
read in this order.

* The carry-less product of two words is the sum of 25 integer products of
  128 bits (`mul`): each word is split into the five classes of its bit
  positions modulo 5. The partial products of class `i` by class `j` all lie
  at positions of class `i + j`, at most 13 at each, which is less than 2⁵:
  their sum does not carry into the next position of the class, so its bit
  there is the carry-less product's. The five products that meet in a class
  are added with XOR, and one mask keeps the class.
* Three such products (Karatsuba) multiply two blocks.
* The four words of the product are reduced with shifts:
  `x¹²⁸ = 1 + x + x² + x⁷`.

`scratch` holds 15 words of the key (`k₀`, `k₁` and `k₀ + k₁`, each in its
five classes), the products of the halves, the callee-saved registers, and
`y₁`, `y₀` and their sum. Every branch and every address depends only on the
pointers and `n`.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64

open VG.X86_64

/-- Word `k` of `scratch`. -/
def slot (k : Nat) : MemOp := { base := .r8, disp := ((8 * k : Nat) : Int) }

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := (d : Int) }

/-- The positions congruent to `r` modulo 5. -/
def mask (r : Nat) : BitVec 64 :=
  match r with
  | 0 => 0x1084210842108421#64 | 1 => 0x2108421084210842#64 | 2 => 0x4210842108421084#64
  | 3 => 0x8421084210842108#64 | _ => 0x0842108421084210#64

/-- The classes of the word being multiplied. -/
def cls (i : Nat) : Reg :=
  match i with
  | 0 => .rcx | 1 => .rbx | 2 => .rbp | 3 => .r12 | _ => .r13

def xorR (d r : Reg) : Instr := .alu .xor d (.reg r)

/-- The slots of `y₁`, `y₀` and their sum, and of the low and high products. -/
def y1S : Nat := 25
def y0S : Nat := 26
def yS : Nat := 27
def lS : Nat := 15
def hS : Nat := 17

def saved : List (Reg × Nat) := [(.rbx, 19), (.rbp, 20), (.r12, 21), (.r13, 22), (.r14, 23), (.r15, 24)]

def save : List Instr := saved.map fun p => .store (slot p.2) p.1
def restore : List Instr := saved.map fun p => .mov p.1 (.mem (slot p.2))

/-! ## The key -/

/-- `H` into `r9` and `r10`; the data pointer and the count out of the way of
the multiplication. -/
def loadH : List Instr :=
  [.mov .r15 (.reg .rdx), .mov .r9 (.mem (at_ .rdi 0)), .mov .r10 (.mem (at_ .rdi 8)), .mov .rdi (.reg .rcx)]

/-- `H · x⁻¹` in `r9` and `r10`, their sum in `r11`. -/
def adjust : List Instr :=
  [.bswap .r9, .bswap .r10,
   .mov .r11 (.reg .r9), .shift .shr .r11 63, .mov .r14 (.reg .r10), .shift .shr .r14 63,
   .shift .shl .r9 1, xorR .r9 .r14, .shift .shl .r10 1, xorR .r10 .r11,
   .shift .shl .r11 57, xorR .r9 .r11, .shift .shl .r11 5, xorR .r9 .r11, .shift .shl .r11 1, xorR .r9 .r11,
   .mov .r11 (.reg .r9), xorR .r11 .r10]

def keyClass (t : Nat) (r : Reg) (j : Nat) : List Instr :=
  [.movImm64 .rax (mask j), .alu .and .rax (.reg r), .store (slot (5 * t + j)) .rax]

def keyWord (t : Nat) (r : Reg) : List Instr := (List.range 5).flatMap (keyClass t r)

def loadY : List Instr :=
  [.mov .r9 (.mem (at_ .rsi 0)), .mov .r10 (.mem (at_ .rsi 8))]

def storeYs : List Instr := [.bswap .r9, .bswap .r10, .store (slot y1S) .r9, .store (slot y0S) .r10]

/-! ## The product of two words -/

/-- The classes of the word in slot `k`. -/
def split1 (k i : Nat) : List Instr := [.movImm64 (cls i) (mask i), .alu .and (cls i) (.mem (slot k))]

def split (k : Nat) : List Instr := (List.range 5).flatMap (split1 k)

/-- Class `i` by the class of key word `t` in slot `5 t + j`, added to `r10 : r9`. -/
def part (t i j : Nat) : List Instr :=
  [.mov .rax (.mem (slot (5 * t + j))), .mul (cls i), xorR .r9 .rax, xorR .r10 .rdx]

/-- The products that meet in class `r`, and that class of their sum, added to
`r14 : r11`. -/
def classSum (t r : Nat) : List Instr :=
  ([xorR .r9 .r9, xorR .r10 .r10] : List Instr) ++ part t 0 (r % 5) ++ part t 1 ((r + 4) % 5) ++
  part t 2 ((r + 3) % 5) ++ part t 3 ((r + 2) % 5) ++ part t 4 ((r + 1) % 5) ++
  ([.movImm64 .rax (mask r), .alu .and .r9 (.reg .rax), .movImm64 .rdx (mask ((r + 1) % 5)),
    .alu .and .r10 (.reg .rdx), xorR .r11 .r9, xorR .r14 .r10] : List Instr)

/-- The carry-less product of the word in slot `k` and key word `t`, in
`r14 : r11`. -/
def mul (k t : Nat) : List Instr :=
  split k ++ ([xorR .r11 .r11, xorR .r14 .r14] : List Instr) ++ classSum t 0 ++ classSum t 1 ++ classSum t 2 ++
  classSum t 3 ++ classSum t 4

def keep (k : Nat) : List Instr := [.store (slot k) .r11, .store (slot (k + 1)) .r14]

/-! ## A block -/

def loadX : List Instr := [.mov .r9 (.mem (at_ .r15 0)), .mov .r10 (.mem (at_ .r15 8))]

def addX : List Instr :=
  [.bswap .r9, .bswap .r10, .alu .xor .r9 (.mem (slot y1S)), .alu .xor .r10 (.mem (slot y0S)),
   .store (slot y1S) .r9, .store (slot y0S) .r10, xorR .r9 .r10, .store (slot yS) .r9]

/-- `d ^= s ≪ 63 ^ s ≪ 62 ^ s ≪ 57`, through `r9`. -/
def foldDn (d s : Reg) : List Instr :=
  [.mov .r9 (.reg s), .shift .shl .r9 57, xorR d .r9, .shift .shl .r9 5, xorR d .r9, .shift .shl .r9 1, xorR d .r9]

/-- `d ^= s ≫ 1 ^ s ≫ 2 ^ s ≫ 7`, through `r9`. -/
def foldUp (d s : Reg) : List Instr :=
  [.mov .r9 (.reg s), .shift .shr .r9 1, xorR d .r9, .shift .shr .r9 1, xorR d .r9, .shift .shr .r9 5, xorR d .r9]

/-- The products, the middle one in `r14 : r11`, reduced and stored as `y₁`
and `y₀`. -/
def reduce : List Instr :=
  ([.mov .rax (.mem (slot lS)), .mov .rdx (.mem (slot (lS + 1))), .mov .rcx (.mem (slot hS)),
    .mov .rbx (.mem (slot (hS + 1))),
    xorR .r11 .rax, xorR .r11 .rcx, xorR .r14 .rdx, xorR .r14 .rbx,
    xorR .r11 .rdx, xorR .r14 .rcx, xorR .r14 .rax] : List Instr) ++
  foldDn .r11 .rax ++ foldUp .r14 .rax ++ ([xorR .rbx .r11] : List Instr) ++ foldUp .rbx .r11 ++ foldDn .r14 .r11 ++
  ([.store (slot y1S) .rbx, .store (slot y0S) .r14] : List Instr)

def next : List Instr := [.alu .add .r15 (.imm 16), .alu .sub .rdi (.imm 1)]

def body : List Instr :=
  loadX ++ addX ++ mul y0S 0 ++ keep lS ++ mul y1S 1 ++ keep hS ++ mul yS 2 ++ reduce ++ next

def prologue : List Instr :=
  save ++ loadH ++ adjust ++ keyWord 0 .r10 ++ keyWord 1 .r9 ++ keyWord 2 .r11 ++ loadY ++ storeYs ++
  ([.alu .test .rdi (.reg .rdi)] : List Instr)

def epilogue : List Instr :=
  ([.mov .r9 (.mem (slot y1S)), .mov .r10 (.mem (slot y0S)), .bswap .r9, .bswap .r10] : List Instr) ++ restore ++
  ([.store (at_ .rsi 0) .r9, .store (at_ .rsi 8) .r10] : List Instr)

def ghash : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop (.block body) .ne)) (.block epilogue))

end VG.Impl.Gcm.X86_64
