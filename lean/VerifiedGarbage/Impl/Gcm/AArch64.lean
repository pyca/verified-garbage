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

`vg_aes_gcm_store_powers_scratch(ctx = x0, pw = x1, scratch = x2)`, with the
multiplication of `vg_ghash` above (`mulCode`); `vg_aes_gcm_store_powers`
runs it with `scratch`, 80 bytes, in a frame of its own
(`Proof/Gcm/AArch64/KeyPowers.lean`).

* `x19`–`x28` are saved in `scratch` and restored on exit, as in `vg_ghash`.
* `setup` computes `H' = x⁻¹ · H` and the masks from the hash subkey `H`,
  bytes 240–255 of the key context, to which `x0` is moved; `H` is also
  loaded into `Z` (`ZH:ZL`).
* `preparedPower(Z)` (`Z` shifted left one bit, `0xc2 ‖ 0¹¹⁸ ‖ 1` XORed in
  under the mask of its top bit) is stored at `x1` as two little-endian
  doublewords, the low first (`storeEnc`): first that of `H`, at `pw + 16`.
* Then, for `k` from 2 to 8, `Z := Z • H` (`mulCode`, of `Y := Z`) and
  `preparedPower(Z)` is stored at `x1 = pw + pwOff k`: pair `j` holds `H²ʲ⁺²`
  at `32 j` and `H²ʲ⁺¹` at `32 j + 16`, so `x1` moves by 48 and by −16 in
  turn, the step kept in `x3` (`32 −` the last one). `x4` counts the powers
  left.
* `x1`–`x4` hold only pointers and counts; no branch and no address depends
  on `H`. -/

/-- The step of `x1` to the next power's place. -/
def D : Reg := .x3
/-- The powers left. -/
def CNT : Reg := .x4

/-- The offset in `pw` of `preparedPower(Hᵏ)`, `1 ≤ k ≤ 8`: pair `j` holds
`H²ʲ⁺²` at `32 j` and `H²ʲ⁺¹` at `32 j + 16`. -/
def pwOff (k : Nat) : Nat := if k % 2 = 0 then 32 * ((k - 2) / 2) else 16 + 32 * ((k - 1) / 2)

def keySave : List Instr := saved.map fun (r, d) => .str .x r .x2 d
def keyRestore : List Instr := saved.map fun (r, d) => .ldr .x r .x2 d

/-- `x0` to `H`, for `setup`. -/
def keyAddr : List Instr := [.addImm .x .x0 .x0 240]

/-- `Z := H`. -/
def keyLoad : List Instr := [
  .ldr .x ZH .x0 0, .rev ZH ZH,
  .ldr .x ZL .x0 8, .rev ZL ZL]

/-- `preparedPower(Z)` stored at `x1 + off`: the mask of the top bit of `Z`
in `B`, the high doubleword in `x0` and the low one in `T`. -/
def storeEnc (off : Nat) : List Instr := [
  .lsr .x T ZH 63, .movz .x B 0 0, .sub .x B B T,
  .lsl .x .x0 ZH 1, .lsr .x T ZL 63, .logic .orr .x .x0 .x0 T,
  .movz .x T 0xc200 3, .logic .and .x T T B, .logic .eor .x .x0 .x0 T,
  .lsl .x T ZL 1, .lsr .x B B 63, .logic .eor .x T T B,
  .str .x T .x1 off, .str .x .x0 .x1 (off + 8)]

/-- The count of the powers after `H`, and the first step. -/
def keyCount : List Instr := [.movz .x CNT 7 0, .movz .x D 48 0]

/-- `Y := Z`, for `mulCode`. -/
def keyY : List Instr := [mov Y0 ZH, mov Y1 ZL, .logic .eor .x YX Y0 Y1]

/-- On to the next power's place. -/
def keyNext : List Instr := [
  .add .x .x1 .x1 D, .movz .x T 32 0, .sub .x D T D, .subImm .x CNT CNT 1]

/-- The next power, stored. -/
def keyBody : List Instr := keyY ++ (mulCode ++ (storeEnc 0 ++ keyNext))

def keyPowers : Prog isa :=
  .seq (.block (keySave ++ (keyAddr ++ (setup ++ (keyLoad ++ (storeEnc 16 ++ keyCount))))))
    (.seq (.loop (.block keyBody) (.nonzero .x CNT)) (.block keyRestore))

end VG.Impl.Gcm.AArch64
