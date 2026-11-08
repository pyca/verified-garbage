module

public import VerifiedGarbage.TCB.PPC64LE.Isa
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

The table `zetaWords` (static `tblSym`) holds `q`, the controls of the
`vperm`s, then the splatted `z` and `z'` of the 63 blocks of `len ≥ 4`, and
the lane zetas of the sixteen groups. `scratch` is unused. Every address is
a pointer plus a constant or a counter, every branch depends on a counter or
a pointer, and the coefficients only reach the vector arithmetic (whose
timing does not depend on its operands, see `TCB/PPC64LE/Isa.lean`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.VNtt

open VG.PPC64LE

/-! ## The table -/

def q : Nat := 8380417

/-- `ζ^BitRev8(m) mod q`. -/
def zeta (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % q

/-- Shoup's constant of `z`. -/
def shoup (z : Nat) : Nat := z * 2 ^ 32 / q

/-- The doubleword of two words, the first the high one. -/
def dw (a b : Nat) : BitVec 64 := BitVec.ofNat 64 (a * 2 ^ 32 + b)

/-- A vector of four word lanes, `[a, b, c, d]` from lane 0, as two
doublewords. -/
def vec4 (a b c d : Nat) : List (BitVec 64) := [dw a b, dw c d]

def splat (x : Nat) : List (BitVec 64) := vec4 x x x x

/-- `vperm` controls: lane `i` of the result is word `k i` of `VA || VB`. -/
def ctl (k₀ k₁ k₂ k₃ : Nat) : List (BitVec 64) :=
  let b := fun k => (4 * k) * 2 ^ 24 + (4 * k + 1) * 2 ^ 16 + (4 * k + 2) * 2 ^ 8 + (4 * k + 3)
  vec4 (b k₀) (b k₁) (b k₂) (b k₃)

/-- The words of the static `tblSym`, by vector (two doublewords each):
0 `q`; 1 the high words of the even and odd products; 2–5 the transpose
(`ca`, `cb`, `cc`, `cd`); `6 + 2(k−1)` and `7 + 2(k−1)` the splatted `z` and
`z'` of block `k ∈ [1, 64)`; `132 + 6g + …` the lane zetas of group `g`:
`len = 2` (`z`, `z'`), `len = 1` of the even pairs and of the odd. -/
def zetaWords : List (BitVec 64) :=
  splat q ++ ctl 0 4 2 6 ++ ctl 0 4 1 5 ++ ctl 2 6 3 7 ++ ctl 0 1 4 5 ++ ctl 2 3 6 7 ++
  (List.range 63).flatMap (fun k => splat (zeta (k + 1)) ++ splat (shoup (zeta (k + 1)))) ++
  (List.range 16).flatMap fun g =>
    let z2 := fun r => zeta (64 + 4 * g + r)
    let za := fun r => zeta (128 + 8 * g + 2 * r)
    let zb := fun r => zeta (128 + 8 * g + 2 * r + 1)
    vec4 (z2 0) (z2 1) (z2 2) (z2 3) ++ vec4 (shoup (z2 0)) (shoup (z2 1)) (shoup (z2 2)) (shoup (z2 3)) ++
    vec4 (za 0) (za 1) (za 2) (za 3) ++ vec4 (shoup (za 0)) (shoup (za 1)) (shoup (za 2)) (shoup (za 3)) ++
    vec4 (zb 0) (zb 1) (zb 2) (zb 3) ++ vec4 (shoup (zb 0)) (shoup (zb 1)) (shoup (zb 2)) (shoup (zb 3))

def tblSym : String := "VG_MLDSA_PPC64LE_NTT_ZETAS"

/-- The next vector of the table, at `r6 + r7`, into `d`; `r7` advances. -/
def ld (d : VReg) : List Instr := [.lxvd2xTbl d .r6 .r7 tblSym zetaWords, .addi .r7 .r7 16]

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

/-- A block: its `z` and `z'`, then `len / 4` steps, then past its upper half. -/
def blockCode : Prog isa :=
  .seq (.block (ld .v2 ++ ld .v3 ++ [.lsr .d .r10 .r8 4]))
    (.seq (.loop (.block stepBody) (.nonzero .d .r10))
      (.block [.add .r5 .r5 .r8, .sub .r12 .r5 .r11]))

/-- A layer: its blocks, from `f`; then `len` halves. -/
def layerCode : Prog isa :=
  .seq (.block [.addi .r5 .r3 0])
    (.seq (.loop blockCode (.nonzero .d .r12)) (.block [.lsr .d .r8 .r8 1, .subi .r12 .r8 8]))

/-- The six layers of `len = 128 … 4`. -/
def wideLayers : Prog isa :=
  .seq (.block [.li .r8 512, .addi .r11 .r3 1024, .li .r9 0])
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
hold coefficients `4r`, `4r+1`, `4r+2`, `4r+3` of the group in lane `r`. -/
def groupBody : List Instr :=
  [.lxvd2x .v8 .r5 .r9, .lxvd2x .v9 .r5 .r8, .lxvd2x .v10 .r5 .r11, .lxvd2x .v11 .r5 .r12] ++
  transpose ++
  ld .v2 ++ ld .v3 ++ bfly .v9 .v11 .v2 .v3 ++ bfly .v8 .v10 .v2 .v3 ++
  ld .v2 ++ ld .v3 ++ bfly .v9 .v8 .v2 .v3 ++
  ld .v2 ++ ld .v3 ++ bfly .v11 .v10 .v2 .v3 ++
  transpose ++
  [.stxvd2x .v8 .r5 .r9, .stxvd2x .v9 .r5 .r8, .stxvd2x .v10 .r5 .r11, .stxvd2x .v11 .r5 .r12,
   .addi .r5 .r5 64, .subi .r10 .r10 1]

def narrowLayers : Prog isa :=
  .seq (.block [.addi .r5 .r3 0, .li .r8 16, .li .r11 32, .li .r12 48, .li .r10 16])
    (.loop (.block groupBody) (.nonzero .d .r10))

/-! ## `vg_mldsa_ntt` -/

/-- The table's address in `r6` (saving `LR` in `r0`), `q`, the controls. -/
def setup : List Instr :=
  [.mflr .r0, .adrSym .r6 tblSym, .mtlr .r0, .li .r7 0] ++
  ld .v4 ++ ld .v5 ++ ld .v16 ++ ld .v17 ++ ld .v18 ++ ld .v19

def ntt : Prog isa := .seq (.block setup) (.seq wideLayers narrowLayers)

end VG.Impl.MlDsa.PPC64LE.VNtt
