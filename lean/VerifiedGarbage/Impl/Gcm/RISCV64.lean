module

public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.Gcm.Clmul

/-!
# GHASH: RISC-V implementation

`vg_ghash(h = a0, y = a1, data = a2, n = a3, scratch = a4)`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H` (SP 800-38D
Algorithm 1, `Spec.Gcm.mul`), as the product of polynomials modulo
`g = x¹²⁸ + x⁷ + x² + x + 1` (`Proof/Gcm/Poly.lean`).

* A 128-bit value is two 64-bit words, loaded big-endian a byte at a time
  (the buffers' alignment the contract does not state), the first holding
  the terms of degree below 64, the bit of `x⁰` its most significant.
* The base ISA has no carry-less multiplication, so the code computes it
  with integer multiplications whose operands have holes (as BearSSL's
  `ghash_ctmul64` does; Thomas Pornin, MIT licence): a 32-bit value is
  split into its four classes of bits modulo 4 (`a ∧ Kᵢ`, `Kᵢ` the bits
  `≡ i mod 4`), and each class `t` of the product is the sum of the four
  integer products of classes adding up to `t`, which at most 8 pairs of
  bits reach, so that no carry reaches the next bit of the class (`holes`).
  A 64-bit product takes three (`pm`, Karatsuba) and a block's three
  (`mulK`, Karatsuba again), then the 256-bit product is reduced modulo `g`
  with shifts (`reduce`), as on x86-64.
* The key is `H · x⁻¹` (`key0`, `key1`): the products of words are those of
  polynomials times `x`. The halves of its two words and of their sum, each
  split into its four classes, are the 36 doublewords at the start of the
  frame, written once (`prep`), and read by every product.
* The frame holds them, the two products a block keeps while it computes
  the third (`spill`), and `s0`–`s9`; it is the 2048 bytes below the stack
  pointer that the contract gives. The prepared key, the spills and the
  saved registers (the caller's) are zeroed before the frame is popped.
* The pointers and the block count are public, and so is everything
  computed from them; no address and no branch depends on anything else.
  The multiplications take secret operands: the M extension's `mul` has no
  operand-dependent timing on the cores this code is for.
-/

@[expose] public section

namespace VG.Impl.Gcm.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadBE64 storeBE)

/-! ## Registers -/

def HP : Reg := .a0
def YP : Reg := .a1
def DP : Reg := .a2
def N : Reg := .a3
/-- `Y`, its two words. -/
def Y0 : Reg := .a4
def Y1 : Reg := .a5
/-- The masks `Kᵢ` of the classes of bits. -/
def K : Nat → Reg
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | _ => .s3
/-- A factor's classes. -/
def Xc : Nat → Reg
  | 0 => .t0 | 1 => .t1 | 2 => .t2 | _ => .t3
/-- The product's classes. -/
def Z : Nat → Reg
  | 0 => .t4 | 1 => .t5 | 2 => .t6 | _ => .s8
/-- The other factor's class, loaded. -/
def B : Reg := .a6
/-- A temporary. -/
def T : Reg := .a7
/-- The 32-bit factor of `holes`. -/
def HA : Reg := .s4
/-- The high half of a 64-bit factor. -/
def XH : Reg := .s5
/-- The low product of `pm`, then its low word. -/
def PL : Reg := .s6
/-- The middle product of `pm`. -/
def PM : Reg := .s7
/-- The frame. -/
def FP : Reg := .s9

/-! ## The frame -/

/-- Doubleword `k` of the frame: `0`–`35` the prepared key (`4 i + j` class
`j` of operand `i`), `36`–`39` the spills, `40`–`49` the saved registers. -/
def slot (k : Nat) : Nat := 8 * k

def saved : List (Reg × Nat) :=
  [(.s0, slot 40), (.s1, slot 41), (.s2, slot 42), (.s3, slot 43), (.s4, slot 44),
   (.s5, slot 45), (.s6, slot 46), (.s7, slot 47), (.s8, slot 48), (.s9, slot 49)]

def frameBytes : Nat := 2048

/-- `sd r, d(t0)` for each saved register. -/
def saveRegs : List Instr := saved.map fun (r, d) => .store .d r .t0 d

/-- `ld r, d(t0)` for each saved register. -/
def restoreRegs : List Instr := saved.map fun (r, d) => .load .d r .t0 d

/-! ## A 32-bit carry-less product -/

/-- `Z₀ := (HA ⊗ b)`'s 64 bits, for the 32-bit `HA` and the 32-bit `b`
whose four classes are at `off(FP)`: `Xᵢ := HA ∧ Kᵢ`, each class `j` of `b`
loaded and multiplied by each `Xᵢ` into `Z_{i + j}`, then each `Zₜ` masked
to its class and the four combined. -/
def holesCode (off : Nat) : List Instr :=
  (List.range 4).map (fun i => .logic .and (Xc i) HA (K i)) ++
  .load .d B FP off :: (List.range 4).map (fun i => .mul (Z i) (Xc i) B) ++
  ((List.range 3).flatMap fun j =>
    .load .d B FP (off + 8 * (j + 1)) ::
      (List.range 4).flatMap fun i => [.mul T (Xc i) B, .logic .xor (Z ((i + j + 1) % 4)) (Z ((i + j + 1) % 4)) T]) ++
  (List.range 4).map (fun t => .logic .and (Z t) (Z t) (K t)) ++
  [.logic .or (Z 0) (Z 0) (Z 1), .logic .or (Z 0) (Z 0) (Z 2), .logic .or (Z 0) (Z 0) (Z 3)]

/-! ## A 64-bit carry-less product -/

/-- `(PL, Z₀) :=` the low and high words of `x ⊗ k` for the 64-bit `x` in
`X`, with `k`'s three operands prepared at `off(FP)`: its halves' products
and Karatsuba's middle one. -/
def pmCode (X : Reg) (off : Nat) : List Instr :=
  [.shift .srl .d XH X 32, .shift .sll .d HA X 32, .shift .srl .d HA HA 32] ++
  holesCode off ++ [.addi PL (Z 0) 0, .logic .xor HA HA XH] ++
  holesCode (off + 64) ++ [.addi PM (Z 0) 0, .addi HA XH 0] ++
  holesCode (off + 32) ++
  [.logic .xor PM PM PL, .logic .xor PM PM (Z 0),
   .shift .sll .d T PM 32, .logic .xor PL PL T, .shift .srl .d T PM 32, .logic .xor (Z 0) (Z 0) T]

/-! ## The key -/

/-- `t0, t1 := H`, then `t3 := key0` and `t5 := key1`. -/
def keyCode : List Instr :=
  loadBE64 .t0 .t2 HP 0 ++ loadBE64 .t1 .t2 HP 8 ++
  [.shift .sll .d .t3 .t0 1, .shift .srl .d .t4 .t1 63, .logic .xor .t3 .t3 .t4,
   .shift .srl .d .t4 .t0 63, .li .t2 0, .sub .t4 .t2 .t4,
   .li .t5 (-62), .shift .sll .d .t5 .t5 56, .logic .and .t5 .t4 .t5, .logic .xor .t3 .t3 .t5,
   .shift .sll .d .t5 .t1 1, .logicImm .and .t6 .t4 1, .logic .xor .t5 .t5 .t6]

/-- The masks: `K₀ = 0x1111…1`, `Kᵢ = K₀ << i`. -/
def maskCode : List Instr :=
  [.lui (K 0) 0x11111, .addi (K 0) (K 0) 0x111, .shift .sll .d T (K 0) 32, .logic .or (K 0) (K 0) T,
   .shift .sll .d (K 1) (K 0) 1, .shift .sll .d (K 2) (K 0) 2, .shift .sll .d (K 3) (K 0) 3]

/-- The four classes of `v` to slots `4 i … 4 i + 3`. -/
def splitStore (v : Reg) (i : Nat) : List Instr :=
  (List.range 4).flatMap fun j => [.logic .and T v (K j), .store .d T FP (slot (4 * i + j))]

/-- Operand `p` (of 3) of the key word in `w`: its low half, its high half
and their sum, each split into classes, as operands `3 p`, `3 p + 1` and `3 p + 2`. -/
def prepWord (w : Reg) (p : Nat) : List Instr :=
  [.shift .sll .d .t6 w 32, .shift .srl .d .t6 .t6 32, .shift .srl .d B w 32, .logic .xor HA .t6 B] ++
  splitStore .t6 (3 * p) ++ splitStore B (3 * p + 1) ++ splitStore HA (3 * p + 2)

/-- The prepared key: `key0`, `key1` and their sum. -/
def prep : List Instr :=
  keyCode ++ maskCode ++ prepWord .t3 0 ++ prepWord .t5 1 ++ [.logic .xor .t4 .t3 .t5] ++ prepWord .t4 2

/-! ## A block -/

/-- `Y := (Y ⊕ X) • H` for the block `X` at `data`: the three products,
their sum and the reduction. -/
def blockCode : List Instr :=
  loadBE64 .t0 .t2 DP 0 ++ loadBE64 .t1 .t2 DP 8 ++
  [.logic .xor Y0 Y0 .t0, .logic .xor Y1 Y1 .t1] ++
  pmCode Y0 (slot 0) ++ [.store .d PL FP (slot 36), .store .d (Z 0) FP (slot 37)] ++
  pmCode Y1 (slot 12) ++ [.store .d PL FP (slot 38), .store .d (Z 0) FP (slot 39)] ++
  [.logic .xor Y0 Y0 Y1] ++ pmCode Y0 (slot 24) ++
  [.load .d .t0 FP (slot 36), .load .d .t1 FP (slot 37), .load .d .t2 FP (slot 38), .load .d .t3 FP (slot 39),
   -- `w₁`, `w₂`
   .logic .xor B (Z 0) .t1, .logic .xor B B .t3, .logic .xor B .t0 B,
   .logic .xor T PL .t0, .logic .xor T T .t2, .logic .xor T T .t3,
   -- `A₂ := foldHi w₂ w₃`
   .shift .sll .d .t4 .t2 63, .logic .xor T T .t4, .shift .sll .d .t4 .t2 62, .logic .xor T T .t4,
   .shift .sll .d .t4 .t2 57, .logic .xor T T .t4,
   -- `B₁ := foldLo w₁ w₃`
   .logic .xor B B .t2, .shift .srl .d .t4 .t2 1, .logic .xor B B .t4, .shift .srl .d .t4 .t2 2,
   .logic .xor B B .t4, .shift .srl .d .t4 .t2 7, .logic .xor B B .t4,
   -- `Y₀ := foldLo w₀ A₂`
   .logic .xor Y0 .t1 T, .shift .srl .d .t4 T 1, .logic .xor Y0 Y0 .t4, .shift .srl .d .t4 T 2,
   .logic .xor Y0 Y0 .t4, .shift .srl .d .t4 T 7, .logic .xor Y0 Y0 .t4,
   -- `Y₁ := foldHi B₁ A₂`
   .shift .sll .d .t4 T 63, .logic .xor Y1 B .t4, .shift .sll .d .t4 T 62, .logic .xor Y1 Y1 .t4,
   .shift .sll .d .t4 T 57, .logic .xor Y1 Y1 .t4,
   .addi DP DP 16, .addi N N (-1)]

/-! ## The function -/

/-- `Y` in. -/
def loadY : List Instr := loadBE64 Y0 .t2 YP 0 ++ loadBE64 Y1 .t2 YP 8

/-- `Y` out. -/
def storeY : List Instr := storeBE 8 Y0 .t2 YP 0 ++ storeBE 8 Y1 .t2 YP 8

/-- The frame's body: the registers saved, the key prepared, `Y` in, the
blocks, `Y` out, the registers restored, and the prepared key, the spills and
the saved registers zeroed. -/
def body : Prog isa :=
  .seq (.block (.addSp .t0 0 :: saveRegs ++ [.addSp FP 0] ++ prep ++ loadY))
    (.seq (.loop (.block blockCode) (.nonzero N))
      (.block (storeY ++ (.addSp .t0 0 :: restoreRegs) ++ Impl.StackScratch.RISCV64.wipe 50)))

def ghash : Prog isa :=
  .ite (.zero N) (.block []) (.frame (.alloc frameBytes) body (.free frameBytes))

end VG.Impl.Gcm.RISCV64
