import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64

/-!
# Poly1305 on AArch64: whole blocks four at a time, in AdvSIMD

`vec` absorbs the first `4 ⌊n / 4⌋` of the `n ≥ 8` whole blocks at `x2`
(`x3` bytes) into the accumulator `x4:x5:x6`, as `Radix64.absorb` would one
at a time, and leaves `x2` at the rest and `x3 mod 64` bytes in `x3`.

* Numbers modulo `p = 2¹³⁰ - 5` are five 26-bit limbs, one per 64-bit lane;
  the accumulator `H` (`v0`–`v4`) has two lanes `A` and `B`, starting at
  `(h, 0)`.
* Each group of four blocks `m₀ … m₃` makes them `A ← (A + m₀) r⁴ + m₂ r²` and
  `B ← (B + m₁) r⁴ + m₃ r²`: the 32-bit lanes of a limb's operand are
  `[A + m₀, B + m₁, m₂, m₃]` and of the multiplier's `[r⁴, r⁴, r², r²]`, so
  `umull`/`umlal` multiply the first two and `umull2`/`umlal2` the last two
  into the same 64-bit lanes. Then `A r + B ≡ r h` for the blocks so far.
  The last group multiplies by `[r⁴, r³, r², r]`, after which `A + B ≡ h`.
* A product `d_k = Σ_{i ≤ k} x_i y_(k-i) + Σ_{i > k} x_i (5 y)_(k+5-i)`
  (`2¹³⁰ ≡ 5`) is carried as in OpenSSL's `poly1305_blocks_neon`, in two
  interleaved chains, leaving each limb below `2²⁶` but `h₁` and `h₄`, which
  are slightly above.
* `r²`, `r³` and `r⁴` are computed by `Radix64`'s multiplication by `r`
  (`mulKey`), from `x4:x5:x6`, after the accumulator has moved to `H`.
* At the end the lanes are added, the limbs put back into three 64-bit words
  with carries, and the third word reduced to at most 4 (`2¹³⁰ ≡ 5`).

Vectors: `H` `v0`–`v4`, products `D` `v16`–`v20`, a pair of blocks' limbs
`v21`–`v25` (the temporary of the carries), the multipliers `R` `v8`–`v12`
and `5 R` `v13`, `v14`, `v5`, `v6` (limbs 1–4), the last group's `v28`–`v31`,
`v7`, the mask `2²⁶ - 1` `v26` and the pad bit `2²⁴` `v27`. The low halves of
the callee-saved `v8`–`v14` are saved in the state's working space (bytes
72–127) and restored. General-purpose registers: those of `Radix64`, `x16`
the mask, `x9`–`x15` temporaries and `x9` the count of groups.

The only branch is on the number of groups, and every address is the data
pointer plus a constant, or the state pointer plus a constant.
-/

namespace VG.Impl.Poly1305.AArch64.Vector

open VG.AArch64


def V (n : Nat) : VReg := VReg.ofNat n
def vo (op : VOp) : Instr := .vop op

/-- The accumulator, the products, a pair of blocks' limbs. -/
def hV (i : Nat) : VReg := V i
def dV (i : Nat) : VReg := V (16 + i)
def iV (i : Nat) : VReg := V (21 + i)
/-- The multipliers and their multiples by 5 (limbs 1–4). -/
def rV (i : Nat) : VReg := V (8 + i)
def sV : Nat → VReg
  | 1 => .v13 | 2 => .v14 | 3 => .v5 | _ => .v6
/-- The last group's multipliers. -/
def fV : Nat → VReg
  | 0 => .v28 | 1 => .v29 | 2 => .v30 | 3 => .v31 | _ => .v7
def maskV : VReg := .v26
def padV : VReg := .v27

/-- The general-purpose registers of the limbs. -/
def X : Nat → Reg
  | 0 => .x9 | 1 => .x10 | 2 => .x11 | 3 => .x12 | _ => .x13

/-- The multiplier of limb `i` of the operand in `d_k`. -/
def mulV (R S : Nat → VReg) (i k : Nat) : VReg := if i ≤ k then R (k - i) else S (k + 5 - i)

/-! ## A group of four blocks -/

/-- The limbs of the blocks at `[x2 + off]` and `[x2 + off + 16]`, lane `j`
of `iV i` holding limb `i` of block `j`, with the pad bit. -/
def split (off : Nat) : List Instr := [
  .ldrq (iV 2) .x2 off, .ldrq (iV 3) .x2 (off + 16),
  vo (.perm .zip1 .d2 (iV 0) (iV 2) (iV 3)), vo (.perm .zip2 .d2 (iV 4) (iV 2) (iV 3)),
  vo (.shift .ushr .d2 (iV 1) (iV 0) 26), vo (.shift .ushr .d2 (iV 2) (iV 0) 52),
  vo (.logic .and (iV 0) (iV 0) maskV), vo (.logic .and (iV 1) (iV 1) maskV),
  vo (.shift .sli .d2 (iV 2) (iV 4) 12), vo (.logic .and (iV 2) (iV 2) maskV),
  vo (.shift .ushr .d2 (iV 3) (iV 4) 14), vo (.logic .and (iV 3) (iV 3) maskV),
  vo (.shift .ushr .d2 (iV 4) (iV 4) 40), vo (.logic .orr (iV 4) (iV 4) padV)]

/-- The low 32 bits of each 64-bit lane of `iV i`, in 32-bit lanes 0–1 and 2–3. -/
def narrow : List Instr := (List.range 5).map fun i => vo (.perm .uzp1 .s4 (iV i) (iV i) (iV i))

/-- A product of the operand `iV i` and the multiplier `M k` into `dV k`, on
32-bit words 0–1 or (`hi`) 2–3: `umull` if `fresh`, else `umlal`. -/
def mac (hi fresh : Bool) (i : Nat) (M : Nat → VReg) (k : Nat) : Instr :=
  if fresh then vo (.umull hi (dV k) (iV i) (M k)) else vo (.umlal hi (dV k) (iV i) (M k))

/-- The products of the second pair of blocks (32-bit words 2 and 3). -/
def prodHi (R S : Nat → VReg) : List Instr :=
  (List.range 5).flatMap fun i => (List.range 5).map (mac true (i == 0) i (mulV R S i))

/-- The accumulator added to the first pair of blocks. -/
def addH : List Instr := (List.range 5).map fun i => vo (.add .d2 (iV i) (iV i) (hV i))

/-- The products of the first pair of blocks, plus the accumulator (32-bit words 0 and 1). -/
def prodLo (R S : Nat → VReg) : List Instr :=
  (List.range 5).flatMap fun i => (List.range 5).map (mac false false i (mulV R S i))

/-- `dst ← src mod 2²⁶` and `next += src / 2²⁶`. -/
def carry1 (src dst next : VReg) : List Instr :=
  [vo (.shift .ushr .d2 (iV 0) src 26), vo (.logic .and dst src maskV), vo (.add .d2 next next (iV 0))]

/-- The products carried into the accumulator. -/
def carry : List Instr :=
  carry1 (dV 0) (hV 0) (dV 1) ++ carry1 (dV 3) (hV 3) (dV 4) ++ carry1 (dV 1) (hV 1) (dV 2) ++
  [vo (.shift .ushr .d2 (iV 0) (dV 4) 26), vo (.logic .and (hV 4) (dV 4) maskV),
    vo (.add .d2 (hV 0) (hV 0) (iV 0)), vo (.shift .shl .d2 (iV 0) (iV 0) 2),
    vo (.add .d2 (hV 0) (hV 0) (iV 0))] ++
  carry1 (dV 2) (hV 2) (hV 3) ++ carry1 (hV 0) (hV 0) (hV 1) ++ carry1 (hV 3) (hV 3) (hV 4)

/-- Four blocks at `x2`, with the multipliers `R` and `S`. -/
def group (R S : Nat → VReg) : List Instr :=
  split 32 ++ narrow ++ prodHi R S ++ split 0 ++ addH ++ narrow ++ prodLo R S ++ carry

/-! ## Setup -/

/-- `2²⁶ - 1` into `x16`. -/
def mask : List Instr := [.movz .x .x16 0xffff 0, .movk .x .x16 0x3ff 1]

/-- The 26-bit limbs of `x4 + 2⁶⁴ x5 + 2¹²⁸ x6` (`x6 ≤ 4`) into `x9`–`x13`. -/
def limbs : List Instr := [
  .logic .and .x .x9 .x4 .x16,
  .lsr .x .x10 .x4 26, .logic .and .x .x10 .x10 .x16,
  .lsr .x .x11 .x4 52, .lsl .x .x12 .x5 12, .logic .orr .x .x11 .x11 .x12,
  .logic .and .x .x11 .x11 .x16,
  .lsr .x .x12 .x5 14, .logic .and .x .x12 .x12 .x16,
  .lsr .x .x13 .x5 40, .lsl .x .x14 .x6 24, .logic .orr .x .x13 .x13 .x14]

/-- The limbs in `x9`–`x13` into 32-bit lane `j` of `dst 0`, …, `dst 4`. -/
def insLimbs (dst : Nat → VReg) (j : Nat) : List Instr :=
  (List.range 5).map fun i => vo (.ins .s4 (dst i) j (X i))

/-- `x4:x5:x6` multiplied by `r`, partially reduced. -/
def mulKey : List Instr := Radix64.products ++ Radix64.combine ++ Radix64.fold ++ Radix64.addLow

/-- The low halves of `v8`–`v14` into the state's working space. -/
def save : List Instr :=
  (List.range 7).flatMap fun k => [.umov .x .x9 (V (8 + k)) 0, .str .x .x9 .x0 (72 + 8 * k)]

def restore : List Instr :=
  (List.range 7).flatMap fun k => [.ldr .x .x9 .x0 (72 + 8 * k), vo (.ins .d2 (V (8 + k)) 0 .x9)]

/-- The accumulator into lane 0 of `H` (lane 1 zero). -/
def loadH : List Instr :=
  limbs ++ (List.range 5).flatMap fun i => [vo (.movi0 (hV i)), vo (.ins .d2 (hV i) 0 (X i))]

/-- The multipliers: `[r⁴, r⁴, r², r²]` in `R`, `[r⁴, r³, r², r]` in the
last group's, and `5 R` in `S`. -/
def powers : List Instr :=
  [.addImm .x .x4 .x7 0, .addImm .x .x5 .x8 0, .movz .x .x6 0 0] ++ limbs ++ insLimbs fV 3 ++
  mulKey ++ limbs ++ insLimbs rV 2 ++ insLimbs rV 3 ++ insLimbs fV 2 ++
  mulKey ++ limbs ++ insLimbs fV 1 ++
  mulKey ++ limbs ++ insLimbs rV 0 ++ insLimbs rV 1 ++ insLimbs fV 0

/-- `S j ← 5 (R j)` for the limbs 1–4. -/
def times5 (R S : Nat → VReg) : List Instr :=
  [1, 2, 3, 4].flatMap fun j => [vo (.shift .shl .s4 (S j) (R j) 2), vo (.add .s4 (S j) (S j) (R j))]

def setup : List Instr :=
  mask ++ save ++ loadH ++ powers ++ times5 rV sV ++
  [vo (.dup .d2 maskV .x16), .movz .x .x9 0x100 1, vo (.dup .d2 padV .x9),
    .lsr .x .x9 .x3 6, .subImm .x .x9 .x9 1]

/-! ## The end -/

/-- The lanes of `H` added, into `x9`–`x13`. -/
def sumLanes : List Instr :=
  (List.range 5).flatMap fun i => [.umov .x (X i) (hV i) 0, .umov .x .x14 (hV i) 1, .add .x (X i) (X i) .x14]

/-- The limbs `x9`–`x13` (each below `2²⁸`) as `x4 + 2⁶⁴ x5 + 2¹²⁸ x6`. -/
def pack : List Instr := [
  .lsl .x .x14 .x10 26, .add .x .x4 .x9 .x14,
  .lsl .x .x14 .x11 52, .adds .x .x4 .x4 .x14,
  .lsr .x .x15 .x11 12, .lsl .x .x14 .x12 14, .add .x .x5 .x15 .x14,
  .lsl .x .x14 .x13 40, .adcs .x .x5 .x5 .x14,
  .lsr .x .x15 .x13 24, .movz .x .x14 0 0, .adc .x .x6 .x15 .x14]

/-- `x6` reduced to at most 4: `2¹³⁰ (x6 / 4)` becomes `5 (x6 / 4)`. -/
def fold6 : List Instr := [
  .lsr .x .x14 .x6 2, .movz .x .x15 3 0, .logic .and .x .x6 .x6 .x15,
  .lsl .x .x15 .x14 2, .add .x .x14 .x14 .x15,
  .adds .x .x4 .x4 .x14, .movz .x .x15 0 0, .adcs .x .x5 .x5 .x15, .adc .x .x6 .x6 .x15]

def finish : List Instr :=
  times5 fV sV ++ group fV sV ++
  [.addImm .x .x2 .x2 64, .movz .x .x9 63 0, .logic .and .x .x3 .x3 .x9] ++
  sumLanes ++ pack ++ fold6 ++ restore

/-- The first `4 ⌊n / 4⌋` of the `n ≥ 8` whole blocks at `x2`. -/
def vec : Prog isa :=
  .seq (.block setup)
  (.seq (.loop (.block (group rV sV ++ [.addImm .x .x2 .x2 64, .subImm .x .x9 .x9 1])) (.nonzero .x .x9))
    (.block finish))

/-! ## `update` -/

/-- The whole blocks of the data at `x2` (`x3` bytes): four at a time in
AdvSIMD if there are at least 8 (below that the scalar code is faster), the rest one at a time. -/
def whole : Prog isa :=
  .seq (.block [.lsr .x .x9 .x3 7])
  (.seq (.ite (.zero .x .x9) (.block []) vec)
    Radix64.whole)

def update : Prog isa :=
  .seq (.block (Radix64.setup ++ [.movz .x .x9 15 0, .logic .and .x .x9 .x1 .x9]))
  (.seq (.ite (.zero .x .x9) (.block []) Radix64.fill)
  (.seq whole
  (.seq Radix64.rest
    (.block (Radix64.reduce ++ Radix64.storeH)))))

end VG.Impl.Poly1305.AArch64.Vector
