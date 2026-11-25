module

public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# GHASH on RISC-V (RV64IM), with integer multiplications

`vg_ghash(h = a0, y = a1, data = a2, n = a3, scratch = a4)`.

A block is two big-endian doublewords, the first `y₁`, whose bit `63 − i` is
the coefficient of `xⁱ`. The key is used as `H · x⁻¹`, which makes up for the
factor `x` of carry-less products of words read in this order.

* The carry-less product of two 32-bit words is the sum of 16 integer
  products (`clmul`): each word is split into the four classes of its bit
  positions modulo 4. The partial products of class `i` by class `j` lie at
  positions of class `i + j`, at most 8 at each, which is less than 2⁴, so
  that a position's sum does not carry into the next of its class. The four
  products that meet in a class are added with XOR and masked once.
* Karatsuba's method, twice, multiplies two blocks with nine of them.
* The product is reduced with shifts: `x¹²⁸ = 1 + x + x² + x⁷`.

The key's nine words in their four classes are 36 doublewords
(`Spec/Gcm/Bitsliced.lean`), which `prep` writes, here in the function's
frame; the loop (`loopCode`) reads them at `a0` and keeps everything else in
registers. `scratch` is not used. Every branch and every address depends only
on the pointers and `n`.
-/

@[expose] public section

namespace VG.Impl.Gcm.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64

def xorI (d n m : Reg) : Instr := .logic .xor d n m
def andI (d n m : Reg) : Instr := .logic .and d n m
def sll (d n : Reg) (k : Nat) : Instr := .shift .sll .d d n k
def srl (d n : Reg) (k : Nat) : Instr := .shift .srl .d d n k
def mv (d n : Reg) : Instr := .addi d n 0

/-- The positions congruent to `j` modulo 4. -/
def mask (j : Nat) : BitVec 64 := 0x1111111111111111#64 <<< j

def maskReg (j : Nat) : Reg :=
  match j with
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | _ => .s3

/-- The masks, the first built and the others shifted from it. -/
def maskCode : List Instr :=
  li64 .s0 .t0 (mask 0) ++ ([sll .s1 .s0 1, sll .s2 .s0 2, sll .s3 .s0 3] : List Instr)

/-! ## The key -/

/-- The hash subkey's address, and the table's. -/
abbrev HP : Reg := .a0
abbrev FP : Reg := .s9

/-- `d ^= s ≪ 63 ^ s ≪ 62 ^ s ≪ 57`, through `t`. -/
def foldDn (d s t : Reg) : List Instr :=
  [sll t s 63, xorI d d t, sll t s 62, xorI d d t, sll t s 57, xorI d d t]

/-- `d ^= s ≫ 1 ^ s ≫ 2 ^ s ≫ 7`, through `t`. -/
def foldUp (d s t : Reg) : List Instr :=
  [srl t s 1, xorI d d t, srl t s 2, xorI d d t, srl t s 7, xorI d d t]

/-- `H · x⁻¹`, from `H`'s words in `t1` and `t2`, in `t4` and `t2`, and the
sum of its words in `t3`. -/
def adjust : List Instr :=
  ([srl .t5 .t1 63, srl .t6 .t2 63, sll .t4 .t1 1, xorI .t4 .t4 .t6, sll .t2 .t2 1, xorI .t2 .t2 .t5] : List Instr) ++
  foldDn .t4 .t5 .t6 ++ ([xorI .t3 .t4 .t2] : List Instr)

def classStore (i : Nat) (r : Reg) (j : Nat) : List Instr :=
  [andI .a7 r (maskReg j), .store .d .a7 FP (8 * (4 * i + j))]

/-- The four classes of the word in `r`, the key's word `i` of 32 bits. -/
def operand (i : Nat) (r : Reg) : List Instr := (List.range 4).flatMap (classStore i r)

/-- The three operands of the doubleword in `r`. -/
def operands (t : Nat) (r : Reg) : List Instr :=
  ([sll .t5 r 32, srl .t5 .t5 32, srl .t6 r 32, xorI .t0 .t5 .t6] : List Instr) ++
  operand (3 * t) .t5 ++ operand (3 * t + 1) .t6 ++ operand (3 * t + 2) .t0

def keyCode : List Instr := maskCode ++ adjust ++ operands 0 .t4 ++ operands 1 .t2 ++ operands 2 .t3

/-- The 36 doublewords at `FP` from the hash subkey at `HP`. -/
def prep : List Instr := loadBE64 .t1 .t0 HP 0 ++ (loadBE64 .t2 .t0 HP 8 ++ keyCode)

/-! ## The product of two 32-bit words -/

/-- The classes of the word being multiplied, and of the key's. -/
def wc (i : Nat) : Reg :=
  match i with
  | 0 => .t0 | 1 => .t1 | 2 => .t2 | _ => .t3

def kc (i : Nat) : Reg :=
  match i with
  | 0 => .t4 | 1 => .t5 | 2 => .t6 | _ => .a5

def classes (x : Reg) (i : Nat) : List Instr :=
  [andI .t0 x .s0, andI .t1 x .s1, andI .t2 x .s2, andI .t3 x .s3,
   .load .d .t4 .a0 (8 * (4 * i + 0)), .load .d .t5 .a0 (8 * (4 * i + 1)),
   .load .d .t6 .a0 (8 * (4 * i + 2)), .load .d .a5 .a0 (8 * (4 * i + 3))]

/-- The first class of the product, in `d`. -/
def classFirst (d : Reg) : List Instr :=
  [.mul d .t0 .t4, .mul .a7 .t1 .a5, xorI d d .a7, .mul .a7 .t2 .t6, xorI d d .a7, .mul .a7 .t3 .t5, xorI d d .a7,
   andI d d .s0]

/-- The class `r` of the product, added to `d`. -/
def classSum (d : Reg) (r : Nat) : List Instr :=
  [.mul .a6 (wc 0) (kc (r % 4)), .mul .a7 (wc 1) (kc ((r + 3) % 4)), xorI .a6 .a6 .a7,
   .mul .a7 (wc 2) (kc ((r + 2) % 4)), xorI .a6 .a6 .a7, .mul .a7 (wc 3) (kc ((r + 1) % 4)), xorI .a6 .a6 .a7,
   andI .a6 .a6 (maskReg r), xorI d d .a6]

/-- The carry-less product of the 32-bit word in `x` and the key's word `i`,
in `d`. -/
def clmul (d x : Reg) (i : Nat) : List Instr :=
  classes x i ++ classFirst d ++ classSum d 1 ++ classSum d 2 ++ classSum d 3

/-- The carry-less product of the doubleword in `w` and the key's doubleword
`t`, in `hi : lo` (`hi` may be `w`). -/
def mul (lo hi w : Reg) (t : Nat) : List Instr :=
  ([sll .s10 w 32, srl .s10 .s10 32] : List Instr) ++ clmul lo .s10 (3 * t) ++ ([srl .s11 w 32] : List Instr) ++
  clmul hi .s11 (3 * t + 1) ++ ([xorI .s10 .s10 .s11] : List Instr) ++ clmul .s8 .s10 (3 * t + 2) ++
  ([xorI .s8 .s8 lo, xorI .s8 .s8 hi, sll .s10 .s8 32, xorI lo lo .s10, srl .s10 .s8 32, xorI hi hi .s10] : List Instr)

/-! ## A block -/

/-- `d = s ^ w ≪ 63 ^ w ≪ 62 ^ w ≪ 57`, through `t`. -/
def foldDnTo (d s w t : Reg) : List Instr :=
  [sll t w 63, xorI s s t, sll t w 62, xorI s s t, sll t w 57, xorI d s t]

/-- The product of `y₁ : y₀` (`s4`, `s5`) and the key, reduced: the sums' product
goes to `s9 : a4`, the first words' to them and `s4`, then the last words'. -/
def core : List Instr :=
  ([xorI .s9 .s4 .s5] : List Instr) ++ mul .a4 .s9 .s9 2 ++ mul .s6 .s4 .s4 0 ++
  ([xorI .a4 .a4 .s6, xorI .s9 .s9 .s4, xorI .s9 .s9 .s6] : List Instr) ++ mul .s6 .s7 .s5 1 ++
  ([xorI .a4 .a4 .s6, xorI .a4 .a4 .s7, xorI .s9 .s9 .s7, xorI .s9 .s9 .s6] : List Instr) ++
  foldDn .a4 .s6 .t0 ++ foldUp .s9 .s6 .t0 ++ ([xorI .s4 .s4 .a4] : List Instr) ++ foldUp .s4 .a4 .t0 ++
  foldDnTo .s5 .s9 .a4 .t0

def loadX : List Instr := loadBE64 .s6 .t0 .a2 0 ++ loadBE64 .s7 .t0 .a2 8

def body : List Instr :=
  loadX ++ ([xorI .s4 .s4 .s6, xorI .s5 .s5 .s7] : List Instr) ++ core ++
  ([.addi .a2 .a2 16, .addi .a3 .a3 (-1)] : List Instr)

def loopCode : Prog isa := .ite (.zero .a3) (.block []) (.loop (.block body) (.nonzero .a3))

/-! ## The functions -/

/-- What the functions keep in their frames, in this order. -/
def saved : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

/-- The registers and their offsets, from `o`. -/
def savedAt (o : Nat) : List (Reg × Nat) := saved.zipIdx.map fun p => (p.1, o + 8 * p.2)

def saveAt (o : Nat) : List Instr := (savedAt o).map fun (r, d) => .store .d r .t0 d
def restoreAt (o : Nat) : List Instr := (savedAt o).map fun (r, d) => .load .d r .t0 d

def loadY : List Instr := loadBE64 .s4 .t0 .a1 0 ++ loadBE64 .s5 .t0 .a1 8

/-- `Y` out of the way, and the registers restored. -/
def finish (o : Nat) : List Instr :=
  ([mv .t1 .s4, mv .t2 .s5, .addSp .t0 0] : List Instr) ++ restoreAt o

/-- `Y` stored, once the frame is released. -/
def storeY : List Instr := storeBE 8 .t1 .t3 .a1 0 ++ (storeBE 8 .t2 .t3 .a1 8 ++ [])

/-- The frame's last 384 bytes are used: the key's words, then the registers. -/
def start : List Instr :=
  ([.addSp .t0 0] : List Instr) ++ saveAt 1952 ++ ([.addSp .s9 1664] : List Instr) ++ prep ++ ([mv .a0 .s9] : List Instr) ++
  loadY

def ghash : Prog isa :=
  .seq (.frame (.alloc 2048) (.seq (.block start) (.seq loopCode (.block (finish 1952)))) (.free 2048)) (.block storeY)

end VG.Impl.Gcm.RISCV64
