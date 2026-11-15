module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# GHASH with the 8-bit PMULL on AArch64

`vg_ghash_neon(h = x0, y = x1, data = x2, n = x3, scratch = x4)`, with the
contract of `vg_ghash` (`Proof.Gcm.ghashAArch64`), for CPUs without
FEAT_PMULL: `pmull` of eight pairs of bytes needs AdvSIMD alone.

The arithmetic is that of `Impl.Gcm.AArch64.Pmull`, one block at a time: a
block is loaded with `ldr q` and `rev64 .16b`, the hash subkey is used as
`H' = H · x⁻¹`, and the 256-bit product of `Y ⊕ X` and `H'` is `x · (Y ⊕ X) ·
H'` in the bit-reflected representation of SP 800-38D.

* The product of two doublewords `a` and `b`, which the 64-bit `pmull`
  computes, is the sum of fifteen `pmull`s of bytes: byte `i` of `a` and
  byte `j` of `b` meet in lane `l` of the `pmull` of `a` shifted down by `d`
  bytes and `b` shifted up by `d` bytes, where `i = l + d` and `j = l - d`,
  and their product then lies at byte `2 l = i + j` of the result, where it
  belongs. That takes seven `pmull`s (`d` from −3 to 3) for the pairs with
  `i + j` even, summed in one register (`P`); the pairs with `i + j` odd
  meet in the eight `pmull`s of `a` shifted down by `d` and `b` shifted up
  by `d - 1` (`d` from −3 to 4), one byte below where they belong, summed
  in another (`Q`), which is then moved up by a byte (`ext #15` of the
  register with itself: its top byte is clear).
* A block's two doublewords are shifted together (`shl`, `ushr` of `.2d`),
  and so are the key's, once per call: `pmull` multiplies the low
  doublewords of a form of the block and a form of the key, and `pmull2`
  the high ones, which gives the products `hi` and `lo` of the halves. The
  third product (Karatsuba) is of the sums of the halves of each: `mid` is it
  plus `hi` and `lo`.
* The reduction folds the lowest doubleword `I₀` of the product
  `I₃ : I₂ : I₁ : I₀` into `I₂` and `I₁`, then `I₁` into `I₃` and `I₂`, with
  shifts: `x¹²⁸ = 1 + x + x² + x⁷`, so `I` contributes `I ⊕ I ≫ 1 ⊕ I ≫ 2 ⊕
  I ≫ 7` to the doubleword two above it and `I ≪ 63 ⊕ I ≪ 62 ⊕ I ≪ 57` to
  the one above.
* `Y` is kept as loaded, and stored with `rev64`.

Only caller-saved registers are used (`x5`, `v0`–`v7`, `v16`–`v31`), and
`scratch` is not. Every branch and every address depends only on the
pointers and `n`.
-/

@[expose] public section

namespace VG.Impl.Gcm.AArch64.Neon

open VG.AArch64

/-! Registers: `v0` `Y`, `v1` the block (then the sum of its halves), `v2`
one of its forms, `v3` a product of bytes, `v4`–`v7` the sums `P` and `Q`
of the low and of the high doublewords, `v16`–`v23` the key shifted by −3
to 4 bytes, `v24`–`v31` the sum of its halves likewise. -/

abbrev Y : VReg := .v0
abbrev A : VReg := .v1
abbrev F : VReg := .v2
abbrev U : VReg := .v3
abbrev P0 : VReg := .v4
abbrev P1 : VReg := .v5
abbrev Q0 : VReg := .v6
abbrev Q1 : VReg := .v7

/-- The key shifted down by `e - 3` bytes (up, if that is negative). -/
def kReg : Nat → VReg
  | 0 => .v16 | 1 => .v17 | 2 => .v18 | 4 => .v20 | 5 => .v21 | 6 => .v22 | 7 => .v23
  | _ => .v19

/-- The sum of the key's halves, shifted likewise. -/
def mReg : Nat → VReg
  | 0 => .v24 | 1 => .v25 | 2 => .v26 | 4 => .v28 | 5 => .v29 | 6 => .v30 | 7 => .v31
  | _ => .v27

/-- `d := n` with each doubleword shifted down by `e - 3` bytes. -/
def form (d n : VReg) : Nat → List Instr
  | 0 => [.vop (.shift .shl .d2 d n 24)]
  | 1 => [.vop (.shift .shl .d2 d n 16)]
  | 2 => [.vop (.shift .shl .d2 d n 8)]
  | 4 => [.vop (.shift .ushr .d2 d n 8)]
  | 5 => [.vop (.shift .ushr .d2 d n 16)]
  | 6 => [.vop (.shift .ushr .d2 d n 24)]
  | 7 => [.vop (.shift .ushr .d2 d n 32)]
  | _ => []

/-- The seven other forms of `k 3`. -/
def forms (k : Nat → VReg) : List Instr :=
  form (k 0) (k 3) 0 ++ form (k 1) (k 3) 1 ++ form (k 2) (k 3) 2 ++ form (k 4) (k 3) 4 ++
    form (k 5) (k 3) 5 ++ form (k 6) (k 3) 6 ++ form (k 7) (k 3) 7

/-- The `pmull`s (`pmull2` if `hi`) of `f` by `k0` and by `k1`, added to
`p` and to `q`. -/
def add2 (hi : Bool) (p q f k0 k1 : VReg) : List Instr :=
  [.vop (.pmull8 hi U f k0), .vop (.logic .eor p p U),
   .vop (.pmull8 hi U f k1), .vop (.logic .eor q q U)]

/-- The `pmull` of `f` by `k1`, added to `q`. -/
def add1 (hi : Bool) (q f k1 : VReg) : List Instr :=
  [.vop (.pmull8 hi U f k1), .vop (.logic .eor q q U)]

/-- `q` moved up by a byte and added to `p`: the product. -/
def fin (p q : VReg) : List Instr := [.vop (.ext q q q 15), .vop (.logic .eor p p q)]

/-- `P0`, `P1` := the products of the low and of the high doublewords of
`A` and the key. The form of `A` shifted down by `d` bytes meets the key
shifted up by `d` (into `P`) and by `d - 1` (into `Q`). -/
def mulLH : List Instr :=
  ([.vop (.pmull8 false P0 A (kReg 3)), .vop (.pmull8 true P1 A (kReg 3)),
    .vop (.pmull8 false Q0 A (kReg 4)), .vop (.pmull8 true Q1 A (kReg 4))] : List Instr) ++
  form F A 4 ++ add2 false P0 Q0 F (kReg 2) (kReg 3) ++ add2 true P1 Q1 F (kReg 2) (kReg 3) ++
  form F A 5 ++ add2 false P0 Q0 F (kReg 1) (kReg 2) ++ add2 true P1 Q1 F (kReg 1) (kReg 2) ++
  form F A 6 ++ add2 false P0 Q0 F (kReg 0) (kReg 1) ++ add2 true P1 Q1 F (kReg 0) (kReg 1) ++
  form F A 7 ++ add1 false Q0 F (kReg 0) ++ add1 true Q1 F (kReg 0) ++
  form F A 2 ++ add2 false P0 Q0 F (kReg 4) (kReg 5) ++ add2 true P1 Q1 F (kReg 4) (kReg 5) ++
  form F A 1 ++ add2 false P0 Q0 F (kReg 5) (kReg 6) ++ add2 true P1 Q1 F (kReg 5) (kReg 6) ++
  form F A 0 ++ add2 false P0 Q0 F (kReg 6) (kReg 7) ++ add2 true P1 Q1 F (kReg 6) (kReg 7) ++
  fin P0 Q0 ++ fin P1 Q1

/-- `Q0` := the product of the sums of the halves of the block (`A` becomes
their sum) and of the key. -/
def mulM : List Instr :=
  ([.vop (.ext F A A 8), .vop (.logic .eor A A F),
    .vop (.pmull8 false Q0 A (mReg 3)), .vop (.pmull8 false Q1 A (mReg 4))] : List Instr) ++
  form F A 4 ++ add2 false Q0 Q1 F (mReg 2) (mReg 3) ++
  form F A 5 ++ add2 false Q0 Q1 F (mReg 1) (mReg 2) ++
  form F A 6 ++ add2 false Q0 Q1 F (mReg 0) (mReg 1) ++
  form F A 7 ++ add1 false Q1 F (mReg 0) ++
  form F A 2 ++ add2 false Q0 Q1 F (mReg 4) (mReg 5) ++
  form F A 1 ++ add2 false Q0 Q1 F (mReg 5) (mReg 6) ++
  form F A 0 ++ add2 false Q0 Q1 F (mReg 6) (mReg 7) ++
  fin Q0 Q1

/-- `mid` (in `Q0`) from the third product, and the product `P0 : Q0 : P1`
reduced into `Y`, as loaded. -/
def reduce : List Instr := [
  .vop (.logic .eor Q0 Q0 P0), .vop (.logic .eor Q0 Q0 P1),
  -- `mid` into `lo` and `hi`
  .vop (.movi0 F),
  .vop (.ext U F Q0 8), .vop (.logic .eor P1 P1 U),
  .vop (.ext U Q0 F 8), .vop (.logic .eor P0 P0 U),
  -- what leaves each doubleword of `lo`
  .vop (.shift .shl .d2 A P1 63), .vop (.shift .shl .d2 U P1 62), .vop (.logic .eor A A U),
  .vop (.shift .shl .d2 U P1 57), .vop (.logic .eor A A U),
  .vop (.ext U F A 8), .vop (.logic .eor P1 P1 U),
  .vop (.ext U A F 8), .vop (.logic .eor P0 P0 U),
  -- what stays
  .vop (.logic .eor P0 P0 P1),
  .vop (.shift .ushr .d2 U P1 1), .vop (.logic .eor P0 P0 U),
  .vop (.shift .ushr .d2 U P1 2), .vop (.logic .eor P0 P0 U),
  .vop (.shift .ushr .d2 U P1 7), .vop (.logic .eor P0 P0 U),
  .vop (.ext Y P0 P0 8)]

/-- The block at `[n, #0]` into `d`, as loaded. -/
def loadRev (d : VReg) (n : Reg) : List Instr := [.ldrq d n 0, .vop (.rev .rev64b d d)]

/-- One block: `Y := (Y ⊕ X) • H`, then the pointer and the count. -/
def body : List Instr :=
  loadRev A .x2 ++ ([.vop (.logic .eor A A Y)] : List Instr) ++ mulLH ++ mulM ++ reduce ++
    ([.addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1] : List Instr)

/-- `H' = H · x⁻¹` from `H` as loaded in `A`, into `kReg 3`: each doubleword
shifted up by a bit, taking the other's top bit (`ushr`, `ext`); the
coefficient of `x⁰` that drops out, the top bit of the low doubleword, adds
`x⁻¹ = x¹²⁷ + x⁶ + x + 1`: its `x¹²⁷` is the bit moved into the high
doubleword, the rest `0xc2 · 2⁵⁶` in the low one, under the mask of that bit
(`sshr`). -/
def twist : List Instr := [
  .vop (.shift .ushr .d2 U A 63), .vop (.shift .shl .d2 F A 1), .vop (.ext P0 U U 8),
  .vop (.logic .eor F F P0),
  .vop (.shift .sshr .d2 P1 A 63),
  .movz .x .x5 0xc200 3, .vop (.movi0 Q0), .vop (.ins .d2 Q0 0 .x5),
  .vop (.logic .and P1 P1 Q0), .vop (.logic .eor (kReg 3) F P1)]

/-- `H'` and its forms, the sum of its halves and its forms, and `Y`. -/
def prologue : List Instr :=
  loadRev A .x0 ++ twist ++
  ([.vop (.ext (mReg 3) (kReg 3) (kReg 3) 8), .vop (.logic .eor (mReg 3) (mReg 3) (kReg 3))] : List Instr) ++
  forms kReg ++ forms mReg ++ loadRev Y .x1

def epilogue : List Instr := [.vop (.rev .rev64b Y Y), .strq Y .x1 0]

def ghash : Prog isa :=
  .ite (.zero .x .x3) (.block [])
    (.seq (.block prologue) (.seq (.loop (.block body) (.nonzero .x .x3)) (.block epilogue)))

end VG.Impl.Gcm.AArch64.Neon
