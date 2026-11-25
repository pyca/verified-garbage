module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# GHASH on x86 (32-bit), in the baseline ISA

`vg_ghash(h, y, data, n, scratch)`, with SSE2 and integer multiplications,
but `pmuludq` (it runs only in an MCDT frame, and the function uses no
stack).

A block is a 128-bit value, its first byte the most significant, so that bit
`127 − i` is the coefficient of `xⁱ`. The key is used as `H · x⁻¹`, which
makes up for the factor `x` of carry-less products of values read in this
order.

* Karatsuba's method, twice, multiplies two blocks with nine products of
  doublewords, of which eight are in the vectors `U₀` (the block) and `U₁`
  (`u1`), and the last, of the sums of all the doublewords, is scalar.
* Each of the eight is three products of words, the halves' and their sums'
  (`U₂`, `u2`): 24 lanes, three vectors (`vecs`). A lane's product of words is
  three products of bytes, eight steps each: a word's top bit, spread by
  `psraw`, is the mask with which the key's byte is added to the double of the
  sum (`eight`).
* The scalar product (`mul32`) is the sum of 16 integer products of 64 bits:
  each word is split into the four classes of its bit positions modulo 4. The
  partial products of class `i` by class `j` lie at positions of class `i + j`,
  at most 8 at each, which is less than 2⁴, so that a position's sum does not
  carry into the next of its class. The four products that meet in a class are
  added with XOR and masked once.
* The product is reduced with shifts of quadwords: `x¹²⁸ = 1 + x + x² + x⁷`.

`scratch` (its address in `ecx`) holds the bytes of the key's vectors, the
classes of the sum of its doublewords and of the block's, `Y`, vectors of the
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

/-- Vector `j` of `scratch`, its words `4 j` to `4 j + 3`. -/
def vslot (j : Nat) : MemOp := at_ .ecx (16 * j)
def vld (d : XReg) (j : Nat) : Instr := .movdquLoad d (vslot j)
def vst (j : Nat) (r : XReg) : Instr := .movdquStore (vslot j) r
def vmv (d r : XReg) : Instr := .xop (.bin .movdqa d r)
def vxor (d r : XReg) : Instr := .xop (.bin .pxor d r)
def vand (d r : XReg) : Instr := .xop (.bin .pand d r)
def vor (d r : XReg) : Instr := .xop (.bin .por d r)
def vaddw (d r : XReg) : Instr := .xop (.bin .paddw d r)
def vsh (op : XShiftOp) (d : XReg) (n : BitVec 8) : Instr := .xop (.shift op d n)

/-- The positions congruent to `j` modulo 4. -/
def mask (j : Nat) : BitVec 32 := 0x11111111#32 <<< j

/-! ## `scratch`: vectors 0 to 5 are the key's bytes -/

/-- The word of the classes of the sum of the key's doublewords, `4 · 6`. -/
def allT : Nat := 6
/-- The words of the classes of the word being multiplied. -/
def wS : Nat := 28
/-- The word and the vector of `Y`. -/
def yS : Nat := 32
def yV : Nat := 8
/-- The vectors of products (`zV` and `uV` of `U₁` and `U₂` before). -/
def xV : Nat := 9
def y'V : Nat := 10
def zV : Nat := 11
def uV : Nat := 12
def wV : Nat := 15
def dpS : Nat := 56
def nS : Nat := 57

def saved : List (Reg × Nat) := [(.ebx, 52), (.esi, 53), (.edi, 54), (.ebp, 55)]
def save : List Instr := saved.map fun p => st p.2 p.1
def restore : List Instr := saved.map fun p => ld p.1 p.2

/-! ## The scalar product of two words -/

/-- Class `j` of the word in `r`, at word `b + j`. -/
def classStore (b : Nat) (r : Reg) (j : Nat) : List Instr :=
  [mv .edx r, .alu .and .edx (.imm (mask j)), st (b + j) .edx]

/-- The four classes of the word in `r`, at words `b` to `b + 3`. -/
def split (b : Nat) (r : Reg) : List Instr :=
  classStore b r 0 ++ classStore b r 1 ++ classStore b r 2 ++ classStore b r 3

/-- Class `i` of the word by class `j` of the key's, at word `4 t`, in
`edx : eax`. -/
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

/-- The words of `Y`. -/
def yWords : List Nat := [32, 33, 34, 35]

/-- The product of the sum of the words `ks` and the key's word, in
`ebp : edi`. -/
def mul32 (ks : List Nat) (t : Nat) : List Instr :=
  sumWords ks ++ split wS .eax ++ classSum t 0 ++ ([mv .edi .ebx, mv .ebp .esi] : List Instr) ++ classSum t 1 ++
  ([xorR .edi .ebx, xorR .ebp .esi] : List Instr) ++ classSum t 2 ++
  ([xorR .edi .ebx, xorR .ebp .esi] : List Instr) ++ classSum t 3 ++ ([xorR .edi .ebx, xorR .ebp .esi] : List Instr)

/-! ## The vectors' products -/

/-- A step: the top bits of `y`'s words, doubled, are the next. -/
def step (y k a m : XReg) : List Instr :=
  [vaddw y y, vmv m y, vsh .psraw m 15, vand m k, vaddw a a, vxor a m]

def steps (y k a m : XReg) : Nat → List Instr
  | 0 => [vmv a y, vsh .psraw a 15, vand a k]
  | n + 1 => steps y k a m n ++ step y k a m

/-- The products of the top bytes of `y`'s words and the bytes `k`, in `a`. -/
def eight (y k a m : XReg) : List Instr := steps y k a m 7

/-- The products of the words of `xmm0` and of the key's vector `j`: the
first four in `xmm4`, the last in `xmm3`. -/
def vecs (j : Nat) : List Instr :=
  ([vmv .xmm1 .xmm0, vsh .psllq .xmm1 8, vxor .xmm1 .xmm0, vld .xmm4 (2 * j + 1)] : List Instr) ++
  eight .xmm0 .xmm4 .xmm2 .xmm6 ++ ([vaddw .xmm0 .xmm0, vld .xmm5 (2 * j)] : List Instr) ++
  eight .xmm0 .xmm5 .xmm3 .xmm6 ++ ([vxor .xmm4 .xmm5] : List Instr) ++ eight .xmm1 .xmm4 .xmm5 .xmm6 ++
  ([vxor .xmm5 .xmm2, vxor .xmm5 .xmm3, vmv .xmm4 .xmm5, vand .xmm4 .xmm7, vxor .xmm5 .xmm4,
    vsh .psllq .xmm4 8, vsh .psrlq .xmm5 8, vxor .xmm3 .xmm4, vxor .xmm2 .xmm5,
    vmv .xmm4 .xmm3, .xop (.bin .punpcklwd .xmm4 .xmm2), .xop (.bin .punpckhwd .xmm3 .xmm2)] : List Instr)

/-- `U₁` and `U₂` of `xmm0`, in `xmm1` and `xmm2`. -/
def us : List Instr :=
  [.xop (.pshufd .xmm1 .xmm0 0x84), .xop (.pshufd .xmm2 .xmm0 0xde), vxor .xmm1 .xmm2,
   vmv .xmm2 .xmm0, vsh .pslld .xmm2 16, vxor .xmm2 .xmm0, vsh .psrld .xmm2 16,
   vmv .xmm3 .xmm1, vsh .pslld .xmm3 16, vxor .xmm3 .xmm1, vsh .psrld .xmm3 16, vsh .pslld .xmm3 16, vor .xmm2 .xmm3]

/-- The middle products `s` (in the low doublewords) added to `q`. -/
def fix (q s : XReg) : List Instr :=
  [vmv .xmm6 q, vsh .psrlq .xmm6 32, vxor .xmm6 q, vxor .xmm6 s, vsh .psllq .xmm6 32, vsh .psrlq .xmm6 16, vxor q .xmm6]

/-- The products, and the scalar one, the halves of the block's in `xmm0` and
`xmm1`. -/
def gather : List Instr :=
  ([vld .xmm0 xV] : List Instr) ++ fix .xmm0 .xmm4 ++ ([vld .xmm1 y'V] : List Instr) ++ fix .xmm1 .xmm3 ++
  ([vsh .psrlq .xmm4 32, vsh .psrlq .xmm3 32, vld .xmm2 zV] : List Instr) ++ fix .xmm2 .xmm4 ++
  ([vld .xmm5 wV] : List Instr) ++ fix .xmm5 .xmm3

def asm : List Instr :=
  [.xop (.movd .xmm6 .edi), .xop (.movd .xmm3 .ebp), .xop (.bin .punpckldq .xmm6 .xmm3),
   .xop (.pshufd .xmm3 .xmm0 0x4e), vxor .xmm3 .xmm0, .xop (.pshufd .xmm4 .xmm1 0x4e), vxor .xmm4 .xmm1,
   .xop (.bin .punpcklqdq .xmm3 .xmm4), vxor .xmm5 .xmm3,
   vmv .xmm3 .xmm5, vxor .xmm3 .xmm2, .xop (.pshufd .xmm4 .xmm3 0x4e), vxor .xmm4 .xmm3, vxor .xmm4 .xmm6,
   vsh .pslldq .xmm4 8, vsh .psrldq .xmm4 4, vxor .xmm4 .xmm2, vxor .xmm4 .xmm0, vxor .xmm4 .xmm1,
   vmv .xmm3 .xmm5, vsh .pslldq .xmm3 8, vsh .psrldq .xmm3 4, vxor .xmm0 .xmm3,
   vmv .xmm3 .xmm4, vsh .pslldq .xmm3 8, vxor .xmm0 .xmm3,
   vsh .psrldq .xmm5 8, vsh .pslldq .xmm5 4, vxor .xmm1 .xmm5, vsh .psrldq .xmm4 8, vxor .xmm1 .xmm4]

/-- `≪ 63`, `≪ 62` and `≪ 57` of `xmm0`'s quadwords, added, in `xmm3`. -/
def dn : List Instr :=
  [vmv .xmm4 .xmm0, vsh .psllq .xmm4 57, vmv .xmm3 .xmm4, vsh .psllq .xmm4 5, vxor .xmm3 .xmm4, vsh .psllq .xmm4 1,
   vxor .xmm3 .xmm4]

/-- The halves reduced, in `xmm1`. -/
def reduce : List Instr :=
  dn ++ ([vsh .pslldq .xmm3 8, vxor .xmm0 .xmm3] : List Instr) ++ dn ++
  ([vsh .psrldq .xmm3 8, vxor .xmm1 .xmm3, vxor .xmm1 .xmm0, vmv .xmm4 .xmm0, vsh .psrlq .xmm4 1, vxor .xmm1 .xmm4,
    vsh .psrlq .xmm4 1, vxor .xmm1 .xmm4, vsh .psrlq .xmm4 5, vxor .xmm1 .xmm4] : List Instr)

/-- The vectors' part of a block, `Y` in `xmm0`. -/
def vpart : List Instr :=
  us ++ ([vst zV .xmm1, vst uV .xmm2] : List Instr) ++ vecs 0 ++ ([vst xV .xmm4, vst y'V .xmm3, vld .xmm0 zV] : List Instr) ++
  vecs 1 ++ ([vst zV .xmm4, vst wV .xmm3, vld .xmm0 uV] : List Instr) ++ vecs 2 ++ gather ++ asm ++ reduce ++
  ([vst yV .xmm1] : List Instr)

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

def storeYs : List Instr := [st (yS + 3) .eax, st (yS + 2) .ebx, st (yS + 1) .esi, st yS .edi]

/-- The bytes of the words of `r`, at vectors `2 j` and `2 j + 1`. -/
def bytes (r : XReg) (j : Nat) : List Instr :=
  [vmv .xmm3 r, vand .xmm3 .xmm7, vxor r .xmm3, vsh .psrlq r 8, vst (2 * j) .xmm3, vst (2 * j + 1) r]

def setC : List Instr := [.mov .eax (.imm 0x00ff00ff), .xop (.movd .xmm7 .eax), .xop (.pshufd .xmm7 .xmm7 0)]

def keyVecs : List Instr :=
  ([vld .xmm0 yV] : List Instr) ++ us ++ bytes .xmm0 0 ++ bytes .xmm1 1 ++ bytes .xmm2 2

def keyCode : List Instr :=
  adjust ++ storeYs ++ sumWords yWords ++ split (4 * allT) .eax ++ setC ++ keyVecs

/-! ## A block -/

/-- The bytes of `xmm0` reversed, through `xmm1`. -/
def rev : List Instr :=
  [vmv .xmm1 .xmm0, vand .xmm1 .xmm7, vxor .xmm0 .xmm1, vsh .psllq .xmm1 8, vsh .psrlq .xmm0 8, vor .xmm0 .xmm1,
   .xop (.pshuflw .xmm0 .xmm0 0x1b), .xop (.pshufhw .xmm0 .xmm0 0x1b), .xop (.pshufd .xmm0 .xmm0 0x4e)]

def loadX : List Instr := [.movdquLoad .xmm0 (at_ .edx 0)]
def advance : List Instr := [.alu .add .edx (.imm 16), st dpS .edx]

/-- The block added to `Y`. -/
def addX : List Instr := rev ++ ([vld .xmm1 yV, vxor .xmm0 .xmm1, vst yV .xmm0] : List Instr)

def next : List Instr := [ld .eax nS, .alu .add .eax (.imm 0xffffffff), st nS .eax]
def test : List Instr := [.alu .test .eax (.reg .eax)]

def body : List Instr :=
  ([ld .edx dpS] : List Instr) ++ loadX ++ advance ++ addX ++ mul32 yWords allT ++ vpart ++ next ++ test

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
