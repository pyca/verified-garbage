module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Poly
public import VerifiedGarbage.Impl.Vector.PPC64LE

/-!
# ML-KEM on PPC64LE: the NTT, its inverse and `MultiplyNTTs`

As on 32-bit ARM (`Impl/MlKem/Arm/Ntt.lean`), with 64-bit registers: the
products of two coefficients (less than `q² < 2²⁴`), and the sums of two of
them in `MultiplyNTTs` (less than `2q² < 2²⁵`), are reduced by `reduce`: the
Barrett reduction `barrett32` (`VG.Proof.MlKem.barrett32`),
`x - ⌊(x >> 11) · 161270 / 2¹⁸⌋ · q`, leaves a value less than `2q`
congruent to `x`, and a subtraction of `q` and a `fixup` finish it.
`r8 = 161270` and `r9 = q` throughout (`consts`).

The table of the `γᵢ` of `MultiplyNTTs` (`gammaTable`) is stored in the
first 512 bytes of `scratch`, as 128 `u32`s (`table`, through `r12`), and
read in order through a pointer. `MultiplyNTTs` uses `r14` and `r15`, which
it saves in `scratch[512..528)` and restores; the functions make no calls, so
the link register is never written, and they use no stack.

* `vg_mlkem_ntt(f = r3, scratch = r4)` and
  `vg_mlkem_inv_ntt(f = r3, scratch = r4)`: on vectors of four coefficients,
  with their own table in `scratch` (below, "`ntt`, four butterflies at a
  time" and "`nttInv`, four inverse butterflies at a time"); they write no
  nonvolatile register.
* `vg_mlkem_multiply_ntts(h = r3, f = r4, g = r5, scratch = r6)`: for each
  pair `i` (counted by `r11`), `h[2i] = f[2i] g[2i] + (f[2i+1] g[2i+1] mod q) γᵢ`
  and `h[2i+1] = f[2i] g[2i+1] + f[2i+1] g[2i]`, each reduced, with `γᵢ`
  read through `r6`.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.PPC64LE

open VG.PPC64LE

/-- `ζ^BitRev7(k) mod q` for `k < 128` (FIPS 203 Appendix A); the proofs check
that it is (`VG.Proof.MlKem.zetas`). -/
def zetaTable : List Nat := [
  1, 1729, 2580, 3289, 2642, 630, 1897, 848, 1062, 1919, 193, 797, 2786, 3260, 569, 1746, 296,
  2447, 1339, 1476, 3046, 56, 2240, 1333, 1426, 2094, 535, 2882, 2393, 2879, 1974, 821, 289, 331,
  3253, 1756, 1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915, 2319, 1435,
  807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648, 2474, 3110, 1227, 910, 17, 2761, 583,
  2649, 1637, 723, 2288, 1100, 1409, 2662, 3281, 233, 756, 2156, 3015, 3050, 1703, 1651, 2789,
  1789, 1847, 952, 1461, 2687, 939, 2308, 2437, 2388, 733, 2337, 268, 641, 1584, 2298, 2037,
  3220, 375, 2549, 2090, 1645, 1063, 319, 2773, 757, 2099, 561, 2466, 2594, 2804, 1092, 403,
  1026, 1143, 2150, 2775, 886, 1722, 1212, 1874, 1029, 2110, 2935, 885, 2154]

/-- `ζ^(2BitRev7(i) + 1) mod q` for `i < 128` (FIPS 203 Appendix A); the proofs
check that it is (`VG.Proof.MlKem.gammas`). -/
def gammaTable : List Nat := [
  17, 3312, 2761, 568, 583, 2746, 2649, 680, 1637, 1692, 723, 2606, 2288, 1041, 1100, 2229, 1409,
  1920, 2662, 667, 3281, 48, 233, 3096, 756, 2573, 2156, 1173, 3015, 314, 3050, 279, 1703, 1626,
  1651, 1678, 2789, 540, 1789, 1540, 1847, 1482, 952, 2377, 1461, 1868, 2687, 642, 939, 2390,
  2308, 1021, 2437, 892, 2388, 941, 733, 2596, 2337, 992, 268, 3061, 641, 2688, 1584, 1745, 2298,
  1031, 2037, 1292, 3220, 109, 375, 2954, 2549, 780, 2090, 1239, 1645, 1684, 1063, 2266, 319,
  3010, 2773, 556, 757, 2572, 2099, 1230, 561, 2768, 2466, 863, 2594, 735, 2804, 525, 1092, 2237,
  403, 2926, 1026, 2303, 1143, 2186, 2150, 1179, 2775, 554, 886, 2443, 1722, 1607, 1212, 2117,
  1874, 1455, 1029, 2300, 2110, 1219, 2935, 394, 885, 2444, 2154, 1175]

/-- `d ← d - ⌊(d >> 11) · 161270 / 2¹⁸⌋ · q`, with `161270` in `r8`, `q` in
`r9` and `t` a temporary. -/
def barrett (d t : Reg) : List Instr :=
  [.lsr .d t d 11, .mul t t .r8, .lsr .d t t 18, .mul t t .r9, .sub d d t]

/-- `d ← d mod q` for `d < 2²⁵`, with `t` a temporary. -/
def reduce (d t : Reg) : List Instr := barrett d t ++ [.sub d d .r9] ++ fixup d t .r9

/-- `r8 = 161270`, `r9 = q`. -/
def consts : List Instr := [.lis .r8 0x2, .ori .r8 .r8 0x75F6, .li .r9 3329]

/-- The 128 entries of `T` as `u32`s at `[b]`, through `r12`. -/
def table (T : List Nat) (b : Reg) : List Instr :=
  (List.range 128).flatMap fun k => [.li .r12 (T.getD k 0), .store .w .r12 b (4 * k)]

/-- Our caller's `r14` and `r15`, stored at `[b, #off]`. -/
def saveRegs (b : Reg) (off : Nat) : List Instr := [.store .d .r14 b off, .store .d .r15 b (off + 8)]

/-- Our caller's `r14` and `r15`, loaded from `[b, #off]`. -/
def restoreRegs (b : Reg) (off : Nat) : List Instr := [.load .d .r14 b off, .load .d .r15 b (off + 8)]

/-! ## `ntt`, four butterflies at a time

The coefficients, `u32`s, are in vectors of four, as `lxvd2x` loads them:
words `1, 0, 3, 2` of a vector (most significant first) are coefficients
`j, …, j + 3` (`swapDwords`). A product by a zeta `z` is Shoup's
(`mulZ`): with `z' = ⌊z · 2³² / q⌋` (`zetaPrime`), `a·z - ⌊a·z' / 2³²⌋·q`
(the high word of each product from `vmuleuw`/`vmulouw`, gathered by
`vperm`) is less than `2q` for `a < q`, congruent to `a·z`; every sum or
difference less than `2q` is reduced by `min(x, x - q)` (`vminuw`).

`scratch` holds the table: word `2k` is `ζ_k`, word `2k + 1` is `ζ'_k`
(`ztable`), `k < 128`. The layers with `len ≥ 4` load a block's pair of words
and splat them (`vspltw`); the last layer, `len = 2`, does two blocks of four
coefficients at a time: their halves are regrouped (`vperm`, `LO` and `HI`)
so that the butterflies' operands are in two vectors, with the two blocks'
zetas picked from the table's vector (`PW`, `PWP`), and regrouped back.

The constant vectors: `q` (`v0`), the high-word gathering control (`v1`),
the regrouping controls (`v2`, `v3`) and the zeta picking controls (`v12`,
`v13`), built from GPRs (`pair`, through `v14`, zero). `r3` = `f` and
`r4` = `scratch` throughout; `r5` and `r6` are the offsets of the two
vectors of a butterfly, `r7` that of the table's next pair, `r9` is `4·len`,
`r10` counts a block's vector butterflies. No nonvolatile register, nor the
link register, is written. -/

/-- `⌊z · 2³² / q⌋`. -/
def zetaPrime (z : Nat) : Nat := z * 2 ^ 32 / 3329

/-- The table: `ζ_k` and `ζ'_k` for each `k`, as `u32`s at `[b]`, through `r12`. -/
def ztable (b : Reg) : List Instr :=
  (List.range 128).flatMap fun k =>
    let z := zetaTable.getD k 0
    let z' := BitVec.ofNat 32 (zetaPrime z)
    [.li .r12 z, .store .w .r12 b (8 * k),
     .lis .r12 (z'.extractLsb' 16 16), .ori .r12 .r12 (z'.extractLsb' 0 16), .store .w .r12 b (8 * k + 4)]

/-- `v8 := t = mulZ(v7)` with the zeta in `v4` and `ζ'` in `v5`. -/
def mulZ : List Instr :=
  [.vop (.mulu false true .v8 .v7 .v5), .vop (.mulu true true .v9 .v7 .v5),
   .vop (.perm .v8 .v8 .v9 .v1), .vop (.muluwm .v9 .v7 .v4), .vop (.muluwm .v8 .v8 .v0),
   .vop (.sub true .v8 .v9 .v8), .vop (.sub true .v9 .v8 .v0), .vop (.minu true .v8 .v8 .v9)]

/-- The butterflies on `v6` and `v7` with the zeta in `v4` (`ζ'` in `v5`):
`t = ζ·v7`, then `v7 = v6 - t`, `v6 = v6 + t`, reduced. -/
def vbfly : List Instr := mulZ ++
  [.vop (.add false .v9 .v6 .v0), .vop (.sub true .v9 .v9 .v8), .vop (.sub true .v10 .v9 .v0),
   .vop (.minu true .v7 .v9 .v10),
   .vop (.add false .v9 .v6 .v8), .vop (.sub true .v10 .v9 .v0), .vop (.minu true .v6 .v9 .v10)]

/-- A vector butterfly of a layer with `len ≥ 4`, on `[r3 + r5]` and `[r3 + r6]`. -/
def vbflyBody : List Instr :=
  [.lxvd2x .v6 .r3 .r5, .lxvd2x .v7 .r3 .r6] ++ vbfly ++
  [.stxvd2x .v6 .r3 .r5, .stxvd2x .v7 .r3 .r6, .addi .r5 .r5 16, .addi .r6 .r6 16, .subi .r10 .r10 1]

/-- A block: its zeta and `ζ'` splatted, then `len / 4` vector butterflies. -/
def vblockCode : Prog isa :=
  .seq (.block [.lxvd2x .v11 .r4 .r7, .vop (.splat true .v4 .v11 1), .vop (.splat true .v5 .v11 0),
      .addi .r7 .r7 8, .add .r6 .r5 .r9, .lsr .d .r10 .r9 4])
    (.seq (.loop (.block vbflyBody) (.nonzero .d .r10))
      (.block [.addi .r5 .r6 0, .subi .r0 .r5 1024]))

/-- A layer with `len ≥ 4`: its blocks. -/
def vlayerCode : Prog isa :=
  .seq (.block [.li .r5 0])
    (.seq (.loop vblockCode (.nonzero .d .r0)) (.block [.lsr .d .r9 .r9 1, .subi .r0 .r9 8]))

/-- Two blocks of the layer with `len = 2`, at `[r3 + r5]` and `[r3 + r6]`,
`r6 = r5 + 16`: regrouped, the butterflies, regrouped back. -/
def vbfly2Body : List Instr :=
  [.lxvd2x .v11 .r4 .r7, .vop (.perm .v4 .v11 .v11 .v12), .vop (.perm .v5 .v11 .v11 .v13),
   .addi .r6 .r5 16, .lxvd2x .v8 .r3 .r5, .lxvd2x .v9 .r3 .r6,
   .vop (.perm .v6 .v8 .v9 .v2), .vop (.perm .v7 .v8 .v9 .v3)] ++ vbfly ++
  [.vop (.perm .v8 .v6 .v7 .v2), .vop (.perm .v9 .v6 .v7 .v3),
   .stxvd2x .v8 .r3 .r5, .stxvd2x .v9 .r3 .r6, .addi .r5 .r5 32, .addi .r7 .r7 16, .subi .r10 .r10 1]

/-- The `vperm` controls (most significant byte first): the high words of
two vectors of products (`v1`); the high or the low doublewords of two
vectors (`v2`, `v3`); words `1, 1, 3, 3` and `0, 0, 2, 2` of one (`v12`, `v13`). -/
def ctlHi : BitVec 128 := 0x000102031011121308090a0b18191a1b
def ctlLo : BitVec 128 := 0x00010203040506071011121314151617
def ctlHi2 : BitVec 128 := 0x08090a0b0c0d0e0f18191a1b1c1d1e1f
def ctlPw : BitVec 128 := 0x0405060704050607_0c0d0e0f0c0d0e0f
def ctlPwp : BitVec 128 := 0x0001020300010203_08090a0b08090a0b

/-- `d := v`, through `r11`, `r12` and `v15`, with `v14` zero. -/
def vconst (d : VReg) (v : BitVec 128) : List Instr :=
  Impl.Vector.PPC64LE.const64 .r11 (v.extractLsb' 64 64) ++ Impl.Vector.PPC64LE.const64 .r12 (v.extractLsb' 0 64) ++
    Impl.Vector.PPC64LE.pair d .v15 .v14 .r11 .r12

/-- `q` in every word. -/
def qVec : BitVec 128 := 0x00000d0100000d0100000d0100000d01

/-- The constants. -/
def vconsts : List Instr :=
  [.vop (.splatImm true .v14 0)] ++ vconst .v0 qVec ++ vconst .v1 ctlHi ++ vconst .v2 ctlLo ++
    vconst .v3 ctlHi2 ++ vconst .v12 ctlPw ++ vconst .v13 ctlPwp

def ntt : Prog isa :=
  .seq (.block (ztable .r4 ++ vconsts ++ ([.li .r7 8, .li .r9 512] : List Instr)))
    (.seq (.loop vlayerCode (.nonzero .d .r0))
      (.seq (.block [.li .r5 0, .li .r10 32]) (.loop (.block vbfly2Body) (.nonzero .d .r10))))

/-! ## `nttInv`, four inverse butterflies at a time

As `ntt`, on the same table and constant vectors, the zetas from `ζ₁₂₇`
down: the last layer's step first (`len = 2`, two blocks at a time, the
second block's coefficients in words `0, 1` so that the table's vector's
words `1` and `3`, `ζₖ` and `ζₖ₊₁`, are the second and the first block's
zetas), then the layers with `len ≥ 4` (`r9 = 4·len` doubled until it is
1024), then every coefficient times `3303` by the same Shoup product, with
`3303` in `v4` and `⌊3303 · 2³² / q⌋` in `v5`. An inverse butterfly is
`x + y` reduced by `min`, and `ζ·(y + q - x)` (`mulZ`, whose input may be
below `2q`). -/

/-- The inverse butterflies on `v6` and `v7` with the zeta in `v4` (`ζ'` in
`v5`): `v6 := (v6 + v7) mod q`, `v8 := ζ·(v7 - v6) mod q`. -/
def vibfly : List Instr :=
  [.vop (.add false .v10 .v6 .v7), .vop (.add false .v7 .v7 .v0), .vop (.sub true .v7 .v7 .v6),
   .vop (.sub true .v6 .v10 .v0), .vop (.minu true .v6 .v10 .v6)] ++ mulZ

/-- A vector inverse butterfly of a layer with `len ≥ 4`, on `[r3 + r5]` and `[r3 + r6]`. -/
def vibflyBody : List Instr :=
  [.lxvd2x .v6 .r3 .r5, .lxvd2x .v7 .r3 .r6] ++ vibfly ++
  [.stxvd2x .v6 .r3 .r5, .stxvd2x .v8 .r3 .r6, .addi .r5 .r5 16, .addi .r6 .r6 16, .subi .r10 .r10 1]

/-- A block: its zeta and `ζ'` splatted, then `len / 4` vector inverse butterflies. -/
def viblockCode : Prog isa :=
  .seq (.block [.lxvd2x .v11 .r4 .r7, .vop (.splat true .v4 .v11 1), .vop (.splat true .v5 .v11 0),
      .subi .r7 .r7 8, .add .r6 .r5 .r9, .lsr .d .r10 .r9 4])
    (.seq (.loop (.block vibflyBody) (.nonzero .d .r10))
      (.block [.addi .r5 .r6 0, .subi .r0 .r5 1024]))

/-- A layer with `len ≥ 4`: its blocks. -/
def vilayerCode : Prog isa :=
  .seq (.block [.li .r5 0])
    (.seq (.loop viblockCode (.nonzero .d .r0)) (.block [.lsl .r9 .r9 1, .subi .r0 .r9 1024]))

/-- Two blocks of the layer with `len = 2`, at `[r3 + r5]` and `[r3 + r6]`,
with the zetas of the table's entries at `[r4 + r7]`. -/
def vibfly2Body : List Instr :=
  [.lxvd2x .v11 .r4 .r7, .vop (.perm .v4 .v11 .v11 .v12), .vop (.perm .v5 .v11 .v11 .v13),
   .addi .r6 .r5 16, .lxvd2x .v8 .r3 .r5, .lxvd2x .v9 .r3 .r6,
   .vop (.perm .v6 .v9 .v8 .v2), .vop (.perm .v7 .v9 .v8 .v3)] ++ vibfly ++
  [.vop (.perm .v9 .v6 .v8 .v2), .vop (.perm .v10 .v6 .v8 .v3),
   .stxvd2x .v9 .r3 .r6, .stxvd2x .v10 .r3 .r5, .addi .r5 .r5 32, .subi .r7 .r7 16, .subi .r10 .r10 1]

/-- `[r3 + r5] ← [r3 + r5] · 3303 mod q`, four coefficients at a time. -/
def vscaleBody : List Instr :=
  [.lxvd2x .v7 .r3 .r5] ++ mulZ ++ [.stxvd2x .v8 .r3 .r5, .addi .r5 .r5 16, .subi .r10 .r10 1]

/-- `3303` in every word, and `⌊3303 · 2³² / q⌋`. -/
def fVec : BitVec 128 := 0x00000ce700000ce700000ce700000ce7
def fpVec : BitVec 128 := 0xfe00275ffe00275ffe00275ffe00275f

def nttInv : Prog isa :=
  .seq (.block (ztable .r4 ++ vconsts ++ ([.li .r7 1008, .li .r5 0, .li .r10 32] : List Instr)))
    (.seq (.loop (.block vibfly2Body) (.nonzero .d .r10))
    (.seq (.block [.li .r7 504, .li .r9 16])
    (.seq (.loop vilayerCode (.nonzero .d .r0))
    (.seq (.block ([.vop (.splatImm true .v14 0)] ++ vconst .v4 fVec ++ vconst .v5 fpVec ++
        ([.li .r5 0, .li .r10 64] : List Instr)))
      (.loop (.block vscaleBody) (.nonzero .d .r10))))))

/-! ## `multiplyNTTs` -/

/-- The pair `i`: `r7 = f[2i]`, `r12 = f[2i+1]`, `r14 = g[2i]`,
`r15 = g[2i+1]`, the sums in `r0`, `γᵢ` and the products in `r10`. -/
def mulBody : List Instr :=
  [.load .w .r7 .r4 0, .load .w .r12 .r4 4, .load .w .r14 .r5 0, .load .w .r15 .r5 4,
   .mul .r0 .r12 .r15] ++ reduce .r0 .r10 ++
  [.load .w .r10 .r6 0, .mul .r0 .r0 .r10, .mul .r10 .r7 .r14, .add .r0 .r10 .r0] ++
  reduce .r0 .r10 ++
  [.store .w .r0 .r3 0, .mul .r0 .r7 .r15, .mul .r10 .r12 .r14, .add .r0 .r0 .r10] ++
  reduce .r0 .r10 ++
  [.store .w .r0 .r3 4, .addi .r3 .r3 8, .addi .r4 .r4 8, .addi .r5 .r5 8, .addi .r6 .r6 4,
   .subi .r11 .r11 1]

def multiplyNTTs : Prog isa :=
  .seq (.block (saveRegs .r6 512 ++ table gammaTable .r6 ++ consts ++ ([.li .r11 128] : List Instr)))
    (.seq (.loop (.block mulBody) (.nonzero .d .r11)) (.block (restoreRegs .r6 0)))

end VG.Impl.MlKem.PPC64LE
