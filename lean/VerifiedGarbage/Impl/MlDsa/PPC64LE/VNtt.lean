module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Vector.PPC64LE
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on PPC64LE: `vg_mldsa_ntt` with VMX

The eight layers of Algorithm 41 four butterflies at a time, on the word
lanes of the vector registers (Power ISA 2.07):

* A butterfly multiplies `b` by its zeta `z` as Shoup does, with
  `z' = ⌊z · 2³² / q⌋`: `hi = ⌊b · z' / 2³²⌋`, the high words of the even
  and odd products (`vmuleuw`, `vmulouw`, then `vperm`), and `r = b·z − hi·q`
  modulo 2³² (`vmuluwm`, `vsubuwm`), which is less than `2q`; then
  `t = min(r, r − q)` (`vminuw`) is `b·z mod q`, `a + t` reduced by
  `min(s, s − q)` and `a − t` by `min(d, d + q)` (`bfly`).
* The layers of `len ≥ 4` load the four coefficients `j … j+3` and the four
  `j+len … j+len+3` of a block (`lxvd2x`, whose lanes are the words of
  memory in the order 1, 0, 3, 2), with the block's `z` and `z'` in every
  lane (`wideLayers`).
* The layers of `len = 2` and `len = 1` take sixteen coefficients at a time
  and transpose their four vectors (`transpose`, eight `vperm`s), so that
  lane `r` holds the four coefficients of block `r` of `len = 2`; each lane
  then has its own zeta (`narrow`).

The `scratch` space holds `z'` of each zeta (`fill`), at `scrK`'s positions:
a block of `len ≥ 4` loads its own and splats it (`vspltw`), a group of
`len = 2` and `len = 1` loads the four of each of its three vectors in lane
order. Since no zeta is 0 modulo `q`, `z = ⌊z' · q / 2³²⌋ + 1` (`zcalc`).
The constants (`q`, the controls of the `vperm`s) are built from immediates
(`consts`). Every address is a pointer plus a constant or a counter, every
branch depends on a counter or a pointer, and the coefficients only reach
the vector arithmetic (whose timing does not depend on its operands, see
`TCB/PPC64LE/Isa.lean`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.VNtt

open VG.PPC64LE

/-! ## The zetas -/

def q : Nat := 8380417

/-- `ζ^BitRev8(m) mod q`. -/
def zeta (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % q

/-- Shoup's constant of `z`. -/
def shoup (z : Nat) : Nat := z * 2 ^ 32 / q

/-- `p XOR 1`. -/
def swap1 (p : Nat) : Nat := if p % 2 = 0 then p + 1 else p - 1

/-- The zeta whose `z'` is at position `p` of `scratch`: block `p` of
`len ≥ 4` at `p`; lane `r` of group `g` at `64 + 4g + (r XOR 1)` (`len = 2`),
`128 + 8g + (r XOR 1)` and `132 + 8g + (r XOR 1)` (`len = 1`, even and odd
pairs). -/
def scrK (p : Nat) : Nat :=
  if p < 64 then p else if p < 128 then swap1 p else
    if (p - 128) % 8 < 4 then 128 + 8 * ((p - 128) / 8) + 2 * swap1 ((p - 128) % 8)
    else 128 + 8 * ((p - 128) / 8) + 2 * swap1 ((p - 128) % 8 - 4) + 1

def scrV (p : Nat) : Nat := shoup (zeta (scrK p))

/-- `r ← v`, its low 32 bits, by `lis` and `ori`. -/
def loadImm (r : Reg) (v : Nat) : List Instr :=
  [.lis r (BitVec.ofNat 16 (v / 65536)), .ori r r (BitVec.ofNat 16 (v % 65536))]

/-- Positions 1 … 255 of `scratch`. -/
def fill : List Instr :=
  (List.range 255).flatMap fun i => loadImm .r12 (scrV (i + 1)) ++ [.store .w .r12 .r4 (4 * (i + 1))]

/-- `d ← hi || lo`, through `r11`, `r12`, `v6` and `v7`. -/
def vconst (d : VReg) (hi lo : Nat) : List Instr :=
  Impl.Vector.PPC64LE.const64 .r12 (BitVec.ofNat 64 hi) ++ Impl.Vector.PPC64LE.const64 .r11 (BitVec.ofNat 64 lo) ++
    [.mtvsrd .v6 .r12, .mtvsrd .v7 .r11, .vop (.sldoi d .v6 .v6 8), .vop (.sldoi d d .v7 8)]

/-- The word of a `vperm` control selecting word `k` of `VA || VB`. -/
def ctlW (k : Nat) : Nat := (4 * k) * 2 ^ 24 + (4 * k + 1) * 2 ^ 16 + (4 * k + 2) * 2 ^ 8 + (4 * k + 3)

/-- A control selecting words `k₀ k₁ k₂ k₃`, into `d`. -/
def ctl (d : VReg) (k₀ k₁ k₂ k₃ : Nat) : List Instr :=
  vconst d (ctlW k₀ * 2 ^ 32 + ctlW k₁) (ctlW k₂ * 2 ^ 32 + ctlW k₃)

/-- `q` in each lane of `v4`; the controls: the high words of the even and
odd products (`v5`), the transpose (`v16 … v19`). -/
def consts : List Instr :=
  loadImm .r12 q ++ [.mtvsrd .v4 .r12, .vop (.splat true .v4 .v4 1)] ++
  ctl .v5 0 4 2 6 ++ ctl .v16 0 4 1 5 ++ ctl .v17 2 6 3 7 ++ ctl .v18 0 1 4 5 ++ ctl .v19 2 3 6 7

/-- `v2 ← z = ⌊z' · q / 2³²⌋ + 1` from `v3 = z'`, lane by lane. -/
def zcalc : List Instr :=
  [.vop (.mulu false true .v6 .v3 .v4), .vop (.mulu true true .v7 .v3 .v4), .vop (.perm .v6 .v6 .v7 .v5),
   .vop (.splatImm true .v7 1), .vop (.add false .v2 .v6 .v7)]

/-! ## The butterfly -/

/-- `(a, b) ← (a + z·b, a − z·b)`, with `z` and `z' = ⌊z · 2³² / q⌋` in each
lane, `q` in `v4` and the control of the high words in `v5`; through `v6`
and `v7`. -/
def bfly (a b z zp : VReg) : List Instr :=
  [.vop (.mulu false true .v6 b zp), .vop (.mulu true true .v7 b zp), .vop (.perm .v6 .v6 .v7 .v5),
   .vop (.muluwm .v7 b z), .vop (.muluwm .v6 .v6 .v4), .vop (.sub true .v7 .v7 .v6),
   .vop (.sub true .v6 .v7 .v4), .vop (.minu true .v7 .v7 .v6),
   .vop (.add false .v6 a .v7), .vop (.sub true b a .v7), .vop (.sub true a .v6 .v4),
   .vop (.minu true a .v6 a), .vop (.add false .v6 b .v4), .vop (.minu true b b .v6)]

/-! ## `len ≥ 4` -/

/-- Four butterflies: `[r5 + r9]` (`r9 = 0`) and `[r5 + r8]` (`r8 = 4·len`). -/
def stepBody : List Instr :=
  [.lxvd2x .v0 .r5 .r9, .lxvd2x .v1 .r5 .r8] ++ bfly .v0 .v1 .v2 .v3 ++
  [.stxvd2x .v0 .r5 .r9, .stxvd2x .v1 .r5 .r8, .addi .r5 .r5 16, .subi .r10 .r10 1]

/-- A block: its `z'` (lane 0 of `[r7]`) and `z`, then `len / 4` steps, then
past its upper half. -/
def blockCode : Prog isa :=
  .seq (.block ([.lxvd2x .v3 .r7 .r9, .vop (.splat true .v3 .v3 0), .addi .r7 .r7 4] ++ zcalc ++
      [.lsr .d .r10 .r8 4]))
    (.seq (.loop (.block stepBody) (.nonzero .d .r10))
      (.block [.add .r5 .r5 .r8, .sub .r12 .r5 .r11]))

/-- A layer: its blocks, from `f`; then `len` halves. -/
def layerCode : Prog isa :=
  .seq (.block [.addi .r5 .r3 0])
    (.seq (.loop blockCode (.nonzero .d .r12)) (.block [.lsr .d .r8 .r8 1, .subi .r12 .r8 8]))

/-- The six layers of `len = 128 … 4`. -/
def wideLayers : Prog isa :=
  .seq (.block [.li .r8 512, .addi .r11 .r3 1024, .li .r9 0, .addi .r7 .r4 0])
    (.loop layerCode (.nonzero .d .r12))

/-! ## `len = 2` and `len = 1` -/

/-- Lane `r` of vector `k` from lane `k` of vector `r`, of `v8 … v11`, through
`v12 … v15`, with the controls in `v16 … v19`. -/
def transpose : List Instr :=
  [.vop (.perm .v12 .v8 .v9 .v16), .vop (.perm .v13 .v8 .v9 .v17),
   .vop (.perm .v14 .v10 .v11 .v16), .vop (.perm .v15 .v10 .v11 .v17),
   .vop (.perm .v8 .v12 .v14 .v18), .vop (.perm .v9 .v12 .v14 .v19),
   .vop (.perm .v10 .v13 .v15 .v18), .vop (.perm .v11 .v13 .v15 .v19)]

/-- Sixteen coefficients at `r5`: `[r5 + r9]`, `[r5 + r8]`, `[r5 + r11]`,
`[r5 + r12]` (`0`, `16`, `32`, `48`). Transposed, `v9`, `v8`, `v11`, `v10`
hold coefficients `4r`, `4r+1`, `4r+2`, `4r+3` of the group in lane `r`. The
`z'` of `len = 2` are at `[r6]`, of `len = 1` at `[r7]` and `[r7 + 16]`. -/
def groupBody : List Instr :=
  [.lxvd2x .v8 .r5 .r9, .lxvd2x .v9 .r5 .r8, .lxvd2x .v10 .r5 .r11, .lxvd2x .v11 .r5 .r12] ++
  transpose ++
  [.lxvd2x .v3 .r6 .r9] ++ zcalc ++ bfly .v9 .v11 .v2 .v3 ++ bfly .v8 .v10 .v2 .v3 ++
  [.lxvd2x .v3 .r7 .r9] ++ zcalc ++ bfly .v9 .v8 .v2 .v3 ++
  [.lxvd2x .v3 .r7 .r8] ++ zcalc ++ [.addi .r6 .r6 16, .addi .r7 .r7 32] ++ bfly .v11 .v10 .v2 .v3 ++
  transpose ++
  [.stxvd2x .v8 .r5 .r9, .stxvd2x .v9 .r5 .r8, .stxvd2x .v10 .r5 .r11, .stxvd2x .v11 .r5 .r12,
   .addi .r5 .r5 64, .subi .r10 .r10 1]

def narrowLayers : Prog isa :=
  .seq (.block [.addi .r5 .r3 0, .li .r8 16, .li .r11 32, .li .r12 48, .li .r10 16, .addi .r6 .r4 256,
      .addi .r7 .r4 512])
    (.loop (.block groupBody) (.nonzero .d .r10))

/-! ## `vg_mldsa_ntt` -/

def ntt : Prog isa := .seq (.block (fill ++ consts)) (.seq wideLayers narrowLayers)

end VG.Impl.MlDsa.PPC64LE.VNtt
