module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# GHASH: ARMv7 implementation

`vg_ghash(h = r0, y = r1, data = r2, n = r3, scratch = [sp])`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H` (SP 800-38D
Algorithm 1, `Spec.Gcm.mul`), as the product of polynomials modulo
`g = x¹²⁸ + x⁷ + x² + x + 1` (`Proof/Gcm/Poly.lean`).

* A 128-bit value is four words, loaded with `ldr` and `rev` (the buffers'
  alignment the contract does not state), the first holding the terms of
  degree below 32, the bit of `x⁰` its most significant.
* The baseline `mul` gives the low 32 bits of a product, so the code
  computes the carry-less product of two 16-bit values, which has 31 bits,
  with integer multiplications whose operands have holes (as BearSSL's
  `ghash_ctmul32` does for the low halves of its products; Thomas Pornin,
  MIT licence): a 16-bit value is split into its three classes of bits
  modulo 3 (`split`), and each class `t` of the product is the sum of the
  three integer products of classes adding up to `t`, which at most 6 pairs
  of bits reach, so that no carry reaches the next bit of the class
  (`core`).
* A 32-bit product takes three of those (`m32`, Karatsuba), a 64-bit one
  three of those (`group`), and a block's three of those (`fin`): 27 in all,
  243 multiplications. Then the 256-bit product is reduced modulo `g` with
  shifts (`fin`).
* The key is `H · x⁻¹` (`prep`): the products of words are those of
  polynomials times `x`. Its four words and the five sums of them that
  Karatsuba's products take are written to the scratch buffer once, and so
  are those of `Y ⊕ X` for every block (`head`).
* The callee-saved registers `r4`–`r11` and `lr` are saved in the first 36
  bytes of the scratch buffer (whose base is kept in `r12`), and `y`, `data`
  and `n` in three other words (`data` and `n` advance there). `Y` stays in
  registers from one block to the next, and is written to `y` at the end.
* The pointers and the block count are public, and so is everything
  computed from them; no address and no branch depends on anything else.
  The multiplications take secret operands: `mul` has no operand-dependent
  timing on the ARMv7 cores (`TCB/Arm/Isa.lean`).
-/

@[expose] public section

namespace VG.Impl.Gcm.Arm

open VG.Arm

/-- The scratch buffer's base. -/
def SB : Reg := .r12
/-- The mask of a product's class 0, `0x49249249`: the bits `≡ 0 mod 3`. -/
def KM : Reg := .r11
/-- The mask of a factor's class 0, `0x9249`: the bits `≡ 0 mod 3` below 16. -/
def KS : Reg := .r10

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 1), (.r6, 2), (.r7, 3), (.r8, 4), (.r9, 5), (.r10, 6), (.r11, 7), (.lr, 8)]

/-- The slots (words of the scratch buffer) of `y`; of the key's nine words;
of `data` and `n`; of the nine words of `Y ⊕ X`; of a product a 32-bit
product keeps while it computes the others; and of the four words of each of
the three 64-bit products. -/
def ySlot : Nat := 9
def kSlot : Nat := 10
def dSlot : Nat := 19
def nSlot : Nat := 20
def xSlot : Nat := 21
def tSlot : Nat := 30
def lSlot : Nat := 31
def hSlot : Nat := 35
def mSlot : Nat := 39

/-! ## A 32-bit carry-less product of 16-bit values -/

/-- The three classes of the low 16 bits of `a`. -/
def split (d0 d1 d2 a : Reg) : List Instr :=
  [.dp .and d0 a (.reg KS), .dp .and d1 a (.shifted KS .lsr 2), .dp .and d2 a (.shifted KS .lsr 1)]

/-- `d :=` the carry-less product of the 16-bit values whose classes are
`r2`, `r3`, `r4` and `r5`, `r6`, `r7`: each class of the product in turn,
masked. Clobbers `r9` and `lr`. -/
def core (d : Reg) : List Instr :=
  [.mul d .r2 .r5, .mul .lr .r3 .r7, .dp .eor d d (.reg .lr), .mul .lr .r4 .r6, .dp .eor d d (.reg .lr),
   .dp .and d d (.reg KM),
   .mul .r9 .r2 .r6, .mul .lr .r3 .r5, .dp .eor .r9 .r9 (.reg .lr), .mul .lr .r4 .r7,
   .dp .eor .r9 .r9 (.reg .lr), .dp .and .r9 .r9 (.shifted KM .lsl 1), .dp .orr d d (.reg .r9),
   .mul .r9 .r2 .r7, .mul .lr .r3 .r6, .dp .eor .r9 .r9 (.reg .lr), .mul .lr .r4 .r5,
   .dp .eor .r9 .r9 (.reg .lr), .dp .and .r9 .r9 (.shifted KM .lsl 2), .dp .orr d d (.reg .r9)]

/-! ## A 64-bit carry-less product of words -/

/-- The words: `r0` and `r1`. -/
def m32Load (xs ks : Nat) : List Instr := [.ldr .r0 SB (4 * xs), .ldr .r1 SB (4 * ks)]

/-- The product of the low halves, kept in the slot `tSlot`. -/
def m32Lo : List Instr :=
  split .r2 .r3 .r4 .r0 ++ (split .r5 .r6 .r7 .r1 ++ (core .r8 ++ ([.str .r8 SB (4 * tSlot)] : List Instr)))

/-- The product of the sums of the halves, in `r8`. -/
def m32Mid : List Instr :=
  .dp .eor .lr .r0 (.shifted .r0 .lsr 16) :: (split .r2 .r3 .r4 .lr ++
    (.dp .eor .lr .r1 (.shifted .r1 .lsr 16) :: (split .r5 .r6 .r7 .lr ++ core .r8)))

/-- The product of the high halves, in `r0`. -/
def m32Hi : List Instr :=
  .mov .lr (.shifted .r0 .lsr 16) :: (split .r2 .r3 .r4 .lr ++
    (.mov .lr (.shifted .r1 .lsr 16) :: (split .r5 .r6 .r7 .lr ++ core .r0)))

/-- Karatsuba's middle term, in `r8`, and the product's two words. -/
def m32Join : List Instr :=
  [.ldr .r1 SB (4 * tSlot), .dp .eor .r8 .r8 (.reg .r1), .dp .eor .r8 .r8 (.reg .r0),
   .dp .eor .r1 .r1 (.shifted .r8 .lsl 16), .dp .eor .r0 .r0 (.shifted .r8 .lsr 16)]

/-- `(r1, r0) :=` the low and high words of the carry-less product of the
words in the slots `xs` and `ks`. -/
def m32 (xs ks : Nat) : List Instr := m32Load xs ks ++ (m32Lo ++ (m32Mid ++ (m32Hi ++ m32Join)))

/-! ## A 128-bit carry-less product -/

/-- The product's two words to the slots `os` and `os + 1`. -/
def st2 (os : Nat) : List Instr := [.str .r1 SB (4 * os), .str .r0 SB (4 * (os + 1))]

/-- The products of the low words and of the high words, from the slots
`os … os + 3`, and Karatsuba's: the product's four words in `r2`–`r5`. -/
def groupJoin (os : Nat) : List Instr :=
  [.ldr .r2 SB (4 * os), .ldr .r3 SB (4 * (os + 1)), .ldr .r4 SB (4 * (os + 2)), .ldr .r5 SB (4 * (os + 3)),
   .dp .eor .r1 .r1 (.reg .r2), .dp .eor .r1 .r1 (.reg .r4), .dp .eor .r0 .r0 (.reg .r3),
   .dp .eor .r0 .r0 (.reg .r5), .dp .eor .r3 .r3 (.reg .r1), .dp .eor .r4 .r4 (.reg .r0)]

/-- `r2`–`r5 :=` the four words of the carry-less product of two 64-bit
values, whose low words, high words and the sums of the two are in the slots
`xs … xs + 2` and `ks … ks + 2`. The slots `os … os + 3` are working space. -/
def group (xs ks os : Nat) : List Instr :=
  m32 xs ks ++ (st2 os ++ (m32 (xs + 1) (ks + 1) ++ (st2 (os + 2) ++ (m32 (xs + 2) (ks + 2) ++ groupJoin os))))

/-- The middle words of a product to their slots. -/
def stMid (os : Nat) : List Instr := [.str .r3 SB (4 * (os + 1)), .str .r4 SB (4 * (os + 2))]

/-! ## A block -/

/-- A register's word XORed with the big-endian word at `off(r2)`. -/
def xorWord (y : Reg) (off : Nat) : List Instr := [.ldr .r3 .r2 off, .rev .r3 .r3, .dp .eor y y (.reg .r3)]

/-- The nine words of Karatsuba's products from the four of a block `w0`–`w3`,
to the slots `s … s + 8`: for the low 64 bits, the high 64 bits and their
sum, the low word, the high word and their sum. Clobbers `t` and `u`. -/
def nine (w0 w1 w2 w3 t u : Reg) (s : Nat) : List Instr :=
  [.str w3 SB (4 * s), .str w2 SB (4 * (s + 1)), .dp .eor t w3 (.reg w2), .str t SB (4 * (s + 2)),
   .str w1 SB (4 * (s + 3)), .str w0 SB (4 * (s + 4)), .dp .eor t w1 (.reg w0), .str t SB (4 * (s + 5)),
   .dp .eor t w3 (.reg w1), .str t SB (4 * (s + 6)), .dp .eor u w2 (.reg w0), .str u SB (4 * (s + 7)),
   .dp .eor t t (.reg u), .str t SB (4 * (s + 8))]

/-- `Y := Y ⊕ X` (in `r1`, `r0`, `lr`, `r10`) for the block `X` at `data`,
which advances. -/
def xorBlock : List Instr :=
  .ldr .r2 SB (4 * dSlot) :: (xorWord .r1 0 ++ (xorWord .r0 4 ++ (xorWord .lr 8 ++
    (xorWord .r10 12 ++ ([.dp .add .r2 .r2 (.imm 16), .str .r2 SB (4 * dSlot)] : List Instr)))))

/-- `Y ⊕ X`, its nine words, and the mask of a factor's classes. -/
def head : List Instr :=
  xorBlock ++ (nine .r1 .r0 .lr .r10 .r2 .r3 xSlot ++ ([.movw KS 0x9249] : List Instr))

/-- `lo := lo ⊕ w ⊕ w·x ⊕ w·x² ⊕ w·x⁷` and `hi :=` what falls off `lo`: the
word `w`, of degrees 128 and more, folded into the two words 128 below. -/
def fold (lo hi w : Reg) : List Instr :=
  [.dp .eor lo lo (.reg w), .dp .eor lo lo (.shifted w .lsr 1), .dp .eor lo lo (.shifted w .lsr 2),
   .dp .eor lo lo (.shifted w .lsr 7), .dp .eor hi hi (.shifted w .lsl 31),
   .dp .eor hi hi (.shifted w .lsl 30), .dp .eor hi hi (.shifted w .lsl 25)]

/-- The 256-bit product from the three 128-bit ones (the low halves' in the
slots `lSlot …`, the high halves' in the slots `hSlot …`, Karatsuba's in
`r2`–`r5`): in `r6`–`r10`, `lr`, `r0`, `r1` from the least significant
word. -/
def finJoin : List Instr :=
  [.ldr .r6 SB (4 * lSlot), .ldr .r7 SB (4 * (lSlot + 1)), .ldr .r8 SB (4 * (lSlot + 2)),
   .ldr .r9 SB (4 * (lSlot + 3)), .ldr .r10 SB (4 * hSlot), .ldr .lr SB (4 * (hSlot + 1)),
   .ldr .r0 SB (4 * (hSlot + 2)), .ldr .r1 SB (4 * (hSlot + 3)),
   .dp .eor .r2 .r2 (.reg .r6), .dp .eor .r2 .r2 (.reg .r10),
   .dp .eor .r3 .r3 (.reg .r7), .dp .eor .r3 .r3 (.reg .lr),
   .dp .eor .r4 .r4 (.reg .r8), .dp .eor .r4 .r4 (.reg .r0),
   .dp .eor .r5 .r5 (.reg .r9), .dp .eor .r5 .r5 (.reg .r1),
   .dp .eor .r8 .r8 (.reg .r2), .dp .eor .r9 .r9 (.reg .r3), .dp .eor .r10 .r10 (.reg .r4),
   .dp .eor .lr .lr (.reg .r5)]

/-- The product's reduction: `Y` in `r1`, `r0`, `lr`, `r10`. -/
def finRed : List Instr :=
  fold .r10 .r9 .r6 ++ (fold .lr .r10 .r7 ++ (fold .r0 .lr .r8 ++ fold .r1 .r0 .r9))

/-- Count the block. -/
def count : List Instr := [.ldr .r2 SB (4 * nSlot), .subs .r2 .r2 (.imm 1), .str .r2 SB (4 * nSlot)]

/-- One block: `Y := (Y ⊕ X) • H`. -/
def blockCode : List Instr :=
  head ++ (group xSlot kSlot lSlot ++ (stMid lSlot ++ (group (xSlot + 3) (kSlot + 3) hSlot ++ (stMid hSlot ++
    (group (xSlot + 6) (kSlot + 6) mSlot ++ (finJoin ++ (finRed ++ count)))))))

/-! ## The function -/

/-- `H` in `r4`–`r7`, and the key `H · x⁻¹` in `r8`, `r9`, `r2`, `r3`. -/
def keyCode : List Instr :=
  [.ldr .r4 .r0 0, .rev .r4 .r4, .ldr .r5 .r0 4, .rev .r5 .r5, .ldr .r6 .r0 8, .rev .r6 .r6,
   .ldr .r7 .r0 12, .rev .r7 .r7,
   .mov .r8 (.shifted .r4 .lsl 1), .dp .eor .r8 .r8 (.shifted .r5 .lsr 31),
   .mov .r9 (.shifted .r5 .lsl 1), .dp .eor .r9 .r9 (.shifted .r6 .lsr 31),
   .mov .r2 (.shifted .r6 .lsl 1), .dp .eor .r2 .r2 (.shifted .r7 .lsr 31),
   .mov .r3 (.shifted .r7 .lsl 1), .dp .eor .r3 .r3 (.shifted .r4 .lsr 31),
   .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.shifted .r4 .lsr 31), .dp .and .r5 .r5 (.imm 0xC2000000),
   .dp .eor .r8 .r8 (.reg .r5)]

/-- The mask of a product's classes, and `Y` in. -/
def loadY : List Instr :=
  [.movw KM 0x9249, .movt KM 0x4924,
   .ldr .r10 .r1 12, .rev .r10 .r10, .ldr .lr .r1 8, .rev .lr .lr, .ldr .r0 .r1 4, .rev .r0 .r0,
   .ldr .r1 .r1 0, .rev .r1 .r1]

/-- The key, its nine words in their slots; the mask; and `Y`. -/
def prep : List Instr := keyCode ++ (nine .r8 .r9 .r2 .r3 .r4 .r5 kSlot ++ loadY)

/-- `Y` out. -/
def storeY : List Instr :=
  [.ldr .r2 SB (4 * ySlot), .rev .r1 .r1, .str .r1 .r2 0, .rev .r0 .r0, .str .r0 .r2 4,
   .rev .lr .lr, .str .lr .r2 8, .rev .r10 .r10, .str .r10 .r2 12]

/-- The stores of the callee-saved registers, and of `y`, `data` and `n`. -/
def saves : List Instr :=
  savedRegs.map (fun (r, k) => Instr.str r SB (4 * k)) ++
    [.str .r1 SB (4 * ySlot), .str .r2 SB (4 * dSlot), .str .r3 SB (4 * nSlot)]

/-- The loads of the callee-saved registers. -/
def restores : List Instr := savedRegs.map fun (r, k) => Instr.ldr r SB (4 * k)

def ghash : Prog isa :=
  .seq (.block (.ldrSp SB 0 :: (saves ++ ([.cmp .r3 (.imm 0)] : List Instr))))
    (.seq (.ite .eq (.block []) (.seq (.block prep) (.seq (.loop (.block blockCode) .ne) (.block storeY))))
      (.block restores))

end VG.Impl.Gcm.Arm
