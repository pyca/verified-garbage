module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# GHASH: AArch64 implementation

`vg_ghash(h = x0, y = x1, data = x2, n = x3, scratch = x4)`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H`, with the
carry-less products computed by integer multiplications with "holes", as in
BearSSL's `ghash_ctmul64.c` (Thomas Pornin, MIT licence; see
<https://www.bearssl.org/ctmul.html>) and in `Impl/Gcm/RISCV64.lean`, whose
mathematics this shares (`Proof/Gcm/Holes.lean`):

* A block is big-endian: each 8-byte half is loaded with `ldr` and `rev`.
  The first half holds the coefficients of `x⁰ … x⁶³` (the most significant
  bit is `x⁰`, SP 800-38D's bit order), the second those of `x⁶⁴ … x¹²⁷`. In
  this bit-reflected order, the integer-style carry-less product of two
  64-bit words `a, b` is the 128-bit word of `x · a · b`.
* The carry-less product of two 32-bit values `a` and `b` (`holesCode`):
  both are split into the four classes of their bits modulo 4 (`a & Kᵢ`,
  `b & Kⱼ`, with the masks `Kᵢ = 0x1111… << i`). The integer product (`mul`)
  of a part of `a` in class `i` and a part of `b` in class `j` has in each
  bit position of class `i + j mod 4` the sum of at most 8 bit products,
  which is less than 16, so its carries never reach the next bit of that
  class: those bits are the bits of the carry-less product. The products of
  each class `t` are added (XOR) in `Zₜ`, masked with `Kₜ` and combined.
* The carry-less product of two 64-bit words (`pmCode`) is three such
  products of their 32-bit halves (Karatsuba).
* `Y • H` is `x⁻¹ · (Y · H)`, so the code multiplies by `H' = x⁻¹ · H`
  instead, computed once (`setup`): `H' = (H <<< 1) ⊕ (x⁻¹ if the bit
  shifted out is 1)`, where `x⁻¹ = 1 + x + x⁶ + x¹²⁷`.
* Each block takes three word products (Karatsuba again): of the first
  halves of `Y ⊕ X` and `H'`, of their second halves, and of the sums of the
  halves of each, which give the 256-bit product `W₀ ‖ W₁ ‖ W₂ ‖ W₃` of
  `x · (Y ⊕ X) · H'` (`W₀` the lowest powers).
* The reduction modulo `x¹²⁸ + x⁷ + x² + x + 1` folds `W₃` into `W₁, W₂`,
  then `W₂` into `W₀, W₁` (`tail`), using `x¹²⁸ = 1 + x + x² + x⁷`.
* `Y` is written back to `y` after every block.
* Everything is in registers, all 28 of the model's but `x30`: `x19`–`x28`
  are saved in `scratch[0..80)` and restored on exit.
* `x1`–`x4` (the pointers and the block count) are public, and `x0` until
  the key is loaded; no address and no branch depends on anything else, and
  `mul` is among the instructions whose time Arm specifies not to depend on
  their operands while PSTATE.DIT is 1 (`TCB/AArch64/Isa.lean`).
-/

@[expose] public section

namespace VG.Impl.Gcm.AArch64

open VG.AArch64

/-- The halves of `Y ⊕ X`, then of the third product. -/
def Y0 : Reg := .x5
def Y1 : Reg := .x6
/-- The sum of the halves of `Y ⊕ X`. -/
def YX : Reg := .x8
/-- The new `Y`. -/
def ZH : Reg := .x7
def ZL : Reg := .x8
/-- The halves of `H' = x⁻¹ · H`. -/
def KW0 : Reg := .x9
def KW1 : Reg := .x10
/-- A class of the second factor. -/
def B : Reg := .x11
/-- A temporary, and the first factor of `holesCode`. -/
def T : Reg := .x12
/-- The second factor of `holesCode`. -/
def HB : Reg := .x26
/-- The first product's words, low and high. -/
def L1 : Reg := .x27
def L2 : Reg := .x7
/-- The second product's. -/
def H1 : Reg := .x28
def H2 : Reg := .x0

/-- The masks of the classes: `Kᵢ = 0x1111111111111111 << i`. -/
def K : Nat → Reg
  | 0 => .x13
  | 1 => .x14
  | 2 => .x15
  | _ => .x16

/-- The classes of the first factor. -/
def Xc : Nat → Reg
  | 0 => .x17
  | 1 => .x19
  | 2 => .x20
  | _ => .x21

/-- The sums of the products of each class. -/
def Z : Nat → Reg
  | 0 => .x22
  | 1 => .x23
  | 2 => .x24
  | _ => .x25

def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- `Z₀` := the carry-less product of the 32-bit values in `T` and `HB`. -/
def holesCode : List Instr :=
  (List.range 4).map (fun i => .logic .and .x (Xc i) T (K i)) ++
  ([.logic .and .x B HB (K 0)] : List Instr) ++ (List.range 4).map (fun i => .mul .x (Z i) (Xc i) B) ++
  (List.range' 1 3).flatMap (fun j => ([.logic .and .x B HB (K j)] : List Instr) ++
    (List.range 4).flatMap fun i =>
      [.mul .x T (Xc i) B, .logic .eor .x (Z ((i + j) % 4)) (Z ((i + j) % 4)) T]) ++
  (List.range 4).map (fun t => .logic .and .x (Z t) (Z t) (K t)) ++
  ([.logic .orr .x (Z 0) (Z 0) (Z 1), .logic .orr .x (Z 0) (Z 0) (Z 2),
    .logic .orr .x (Z 0) (Z 0) (Z 3)] : List Instr)

/-- `d` := the low 32 bits of `X`. -/
def lo32 (d X : Reg) : List Instr := [.lsl .x d X 32, .lsr .x d d 32]

/-- `OH:OL` := the carry-less product of the words `X` and `Y`: the products
of their low halves, of their high halves and of the sums of their halves. -/
def pmCode (X Y OL OH : Reg) : List Instr :=
  lo32 T X ++ lo32 HB Y ++ holesCode ++
  ([mov OL (Z 0), .lsr .x T X 32, .lsr .x HB Y 32] : List Instr) ++ holesCode ++
  ([mov OH (Z 0)] : List Instr) ++ lo32 T X ++ ([.lsr .x B X 32, .logic .eor .x T T B] : List Instr) ++
  lo32 HB Y ++ ([.lsr .x B Y 32, .logic .eor .x HB HB B] : List Instr) ++ holesCode ++
  ([.logic .eor .x (Z 0) (Z 0) OL, .logic .eor .x (Z 0) (Z 0) OH,
    .lsl .x T (Z 0) 32, .logic .eor .x OL OL T,
    .lsr .x T (Z 0) 32, .logic .eor .x OH OH T] : List Instr)

/-- The registers saved in `scratch`, and where. -/
def saved : List (Reg × Nat) :=
  [(.x19, 0), (.x20, 8), (.x21, 16), (.x22, 24), (.x23, 32), (.x24, 40), (.x25, 48), (.x26, 56),
   (.x27, 64), (.x28, 72)]

def save : List Instr := saved.map fun (r, d) => .str .x r .x4 d
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x4 d

/-- `H' = x⁻¹ · H` in `KW0`, `KW1`, and the masks. -/
def setup : List Instr := [
  .ldr .x KW0 .x0 0, .rev KW0 KW0,
  .ldr .x KW1 .x0 8, .rev KW1 KW1,
  -- `B` := all ones if the bit shifted out is set
  .lsr .x T KW0 63, .movz .x B 0 0, .sub .x B B T,
  .lsl .x KW0 KW0 1, .lsr .x T KW1 63, .logic .eor .x KW0 KW0 T,
  .movz .x T 0xc200 3, .logic .and .x T B T, .logic .eor .x KW0 KW0 T,
  .lsl .x KW1 KW1 1, .movz .x T 1 0, .logic .and .x T B T, .logic .eor .x KW1 KW1 T,
  .movz .x (K 0) 0x1111 0, .movk .x (K 0) 0x1111 1, .movk .x (K 0) 0x1111 2,
  .movk .x (K 0) 0x1111 3,
  .lsl .x (K 1) (K 0) 1, .lsl .x (K 2) (K 0) 2, .lsl .x (K 3) (K 0) 3]

/-- Load `Y ⊕ X` and the sum of its halves. -/
def load : List Instr := [
  .ldr .x Y0 .x1 0, .rev Y0 Y0,
  .ldr .x T .x2 0, .rev T T,
  .logic .eor .x Y0 Y0 T,
  .ldr .x Y1 .x1 8, .rev Y1 Y1,
  .ldr .x T .x2 8, .rev T T,
  .logic .eor .x Y1 Y1 T,
  .logic .eor .x YX Y0 Y1]

/-- The four words of the product, from the three products (the third in
`Y1:Y0`), and its reduction, into `ZH:ZL`. -/
def tail : List Instr := [
  -- `W₁` in `YX`, `W₂` in `B`; `W₀` is `L2` and `W₃` is `H1`
  .logic .eor .x YX Y1 L2, .logic .eor .x YX YX H2, .logic .eor .x YX L1 YX,
  .logic .eor .x B Y0 L1, .logic .eor .x B B H1, .logic .eor .x B B H2,
  -- `W₃` into `W₂` and `W₁`
  .lsl .x T H1 63, .logic .eor .x B B T, .lsl .x T H1 62, .logic .eor .x B B T,
  .lsl .x T H1 57, .logic .eor .x B B T,
  .logic .eor .x YX YX H1, .lsr .x T H1 1, .logic .eor .x YX YX T, .lsr .x T H1 2,
  .logic .eor .x YX YX T, .lsr .x T H1 7, .logic .eor .x YX YX T,
  -- `W₂` into `W₀` and `W₁`
  .logic .eor .x ZH L2 B, .lsr .x T B 1, .logic .eor .x ZH ZH T, .lsr .x T B 2,
  .logic .eor .x ZH ZH T, .lsr .x T B 7, .logic .eor .x ZH ZH T,
  .lsl .x T B 63, .logic .eor .x ZL YX T, .lsl .x T B 62, .logic .eor .x ZL ZL T,
  .lsl .x T B 57, .logic .eor .x ZL ZL T]

/-- `ZH:ZL := (Y ⊕ X) • H`: the three products, the third by the sum of the
halves of `H'`, which is in `KW0` meanwhile. -/
def mulCode : List Instr :=
  pmCode Y0 KW0 L1 L2 ++ pmCode Y1 KW1 H1 H2 ++
  ([.logic .eor .x KW0 KW0 KW1] : List Instr) ++ pmCode YX KW0 Y0 Y1 ++
  ([.logic .eor .x KW0 KW0 KW1] : List Instr) ++ tail

/-- Store `Z` as the new `Y`, advance to the next block and count it. -/
def store : List Instr := [
  .rev ZH ZH, .str .x ZH .x1 0,
  .rev ZL ZL, .str .x ZL .x1 8,
  .addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1]

/-- One block. -/
def body : List Instr := load ++ mulCode ++ store

def ghash : Prog isa :=
  .ite (.zero .x .x3) (.block [])
    (.seq (.block (save ++ setup))
      (.seq (.loop (.block body) (.nonzero .x .x3)) (.block restore)))

/-! ## The powers from a key context

`vg_aes_gcm_store_powers(ctx = x0, pw = x1)`, with SP 800-38D Algorithm 1 bit
by bit, as `Spec.Gcm.mul` defines it (no PMULL, and no scratch buffer for the
registers the multiplication above needs):

* A 128-bit value is kept in two registers, `hi` (the first eight bytes)
  and `lo`.
* The factor `X` is in `x5:x6`. Each step takes its most significant bit
  `xᵢ` (`lsr` by 63), turns it into the mask `m = 0 − xᵢ`, and shifts it
  left by one bit.
* `Z` (in `x7:x8`) accumulates `V & m`, so `Z := Z ⊕ V` exactly when
  `xᵢ = 1`.
* `V` (in `x9:x10`, starting at `H`) is shifted right by one bit, and the
  reduction constant `R` (the high half `0xE1 ‖ 0⁵⁶`, in `x13`) is XORed
  into it under the mask `0 − LSB₁(V)`.
* The 128 steps are a loop of `unroll` steps per iteration, counted down in
  `x14`; `x15` holds zero.

The hash subkey `H`, bytes 240–255 of the key context, is loaded
into `x2:x3` and `Z`; then for `k` from 1 to 8,
`preparedPower(Hᵏ)` (`Z` shifted left one bit, `0xc2 ‖ 0¹¹⁸ ‖ 1` XORed
in under the mask of its top bit) stored at `pwOff k` as two little-endian
doublewords, the low first, and, below 8, `Z := Z • H` by the loop of
steps, from `X := Z`, `V := H`. Only caller-saved registers are used
(`x2`–`x15`); no branch and no address depends on `H`. -/

/-- `Y ⊕ X`, shifted left one bit per step. -/
def XH : Reg := .x5
def XL : Reg := .x6
/-- `V` (the product so far, `Z`, is in `ZH:ZL`). -/
def VH : Reg := .x9
def VL : Reg := .x10
/-- The masks `−xᵢ` and `−LSB₁(V)`. -/
def M : Reg := .x11
/-- The high half of `R`. -/
def RH : Reg := .x13
/-- The loop counter. -/
def CNT : Reg := .x14
/-- Zero. -/
def ZERO : Reg := .x15

/-- The high half of `R = 11100001 ‖ 0¹²⁰` (its low half is 0). -/
def rHigh : BitVec 64 := 0xE100000000000000

/-- Steps per iteration of the inner loop. -/
def unroll : Nat := 8

/-- One step `i` of Algorithm 1. -/
def step : List Instr := [
  -- M := −xᵢ, and X := X << 1
  .lsr .x T XH 63,
  .sub .x M ZERO T,
  .lsl .x XH XH 1,
  .lsr .x T XL 63,
  .logic .orr .x XH XH T,
  .lsl .x XL XL 1,
  -- Z := Z ⊕ (V ∧ M)
  .logic .and .x T VH M,
  .logic .eor .x ZH ZH T,
  .logic .and .x T VL M,
  .logic .eor .x ZL ZL T,
  -- M := −LSB₁(V)
  .lsl .x T VL 63,
  .lsr .x T T 63,
  .sub .x M ZERO T,
  -- V := (V >> 1) ⊕ (R ∧ M)
  .lsr .x VL VL 1,
  .lsl .x T VH 63,
  .logic .orr .x VL VL T,
  .lsr .x VH VH 1,
  .logic .and .x M M RH,
  .logic .eor .x VH VH M]

/-- `unroll` steps, then the count. -/
def steps : List Instr :=
  (List.range unroll).flatMap (fun _ => step) ++ ([.subImm .x CNT CNT 1] : List Instr)

/-- The offset in `pw` of `preparedPower(Hᵏ)`, `1 ≤ k ≤ 8`: pair `j` holds
`H²ʲ⁺²` at `32 j` and `H²ʲ⁺¹` at `32 j + 16`. -/
def pwOff (k : Nat) : Nat := if k % 2 = 0 then 32 * ((k - 2) / 2) else 16 + 32 * ((k - 1) / 2)

/-- `H` into `x2:x3` and `Z`, with `R` and zero. -/
def keyLoad : List Instr := [
  .movz .x RH 0xE100 3, .movz .x ZERO 0 0,
  .ldr .x .x2 .x0 240, .rev .x2 .x2,
  .ldr .x .x3 .x0 248, .rev .x3 .x3,
  .logic .orr .x ZH .x2 ZERO, .logic .orr .x ZL .x3 ZERO]

/-- `preparedPower(Z)` stored at `pw + off`: the high doubleword in `x4`,
the low one in `T`. -/
def storeEnc (off : Nat) : List Instr := [
  .lsr .x T ZH 63, .sub .x M ZERO T,
  .lsl .x .x4 ZH 1, .lsr .x T ZL 63, .logic .orr .x .x4 .x4 T,
  .movz .x VH 0xc200 3, .logic .and .x VH VH M, .logic .eor .x .x4 .x4 VH,
  .lsl .x T ZL 1, .lsr .x VL M 63, .logic .eor .x T T VL,
  .str .x T .x1 off, .str .x .x4 .x1 (off + 8)]

/-- `X := Z`, `V := H`, `Z := 0` and the count, for `Z • H`. -/
def nextMul : List Instr := [
  .logic .orr .x XH ZH ZERO, .logic .orr .x XL ZL ZERO,
  .logic .orr .x VH .x2 ZERO, .logic .orr .x VL .x3 ZERO,
  .movz .x ZH 0 0, .movz .x ZL 0 0,
  .movz .x CNT (BitVec.ofNat 16 (128 / unroll)) 0]

/-- `preparedPower(Hᵏ)` stored, then `Hᵏ⁺¹`. -/
def keyRound (k : Nat) : Prog isa :=
  .seq (.block (storeEnc (pwOff k) ++ nextMul)) (.loop (.block steps) (.nonzero .x CNT))

def keyPowers : Prog isa :=
  .seq (.block keyLoad) (.seq (keyRound 1) (.seq (keyRound 2) (.seq (keyRound 3)
    (.seq (keyRound 4) (.seq (keyRound 5) (.seq (keyRound 6) (.seq (keyRound 7)
      (.block (storeEnc (pwOff 8))))))))))

end VG.Impl.Gcm.AArch64
