module

public import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-KEM on AArch64: `MultiplyNTTs`, `add` and `sub`

These compute on four coefficients at a time, in the 32-bit lanes of
vectors (see "Vectors"); the NTT and its inverse, on eight in 16-bit lanes,
are in `Ntt16.lean`.

The tables of `ζ^BitRev7(k)` (`zetas`) and of the `γᵢ` of `MultiplyNTTs`
(`gammas`) are stored in `scratch` first, as 128 `u32`s (`table`).

* `multiplyNTTs(h = x0, f = x1, g = x2, scratch = x3)`: for each pair,
  `h[2i] = f[2i] g[2i] + (f[2i+1] g[2i+1] mod q) γᵢ` and
  `h[2i+1] = f[2i] g[2i+1] + f[2i+1] g[2i]`, each reduced, four pairs at a
  time in vectors (`vmulBody`).
* `add(f = x0, g = x1)`, `sub(f = x0, g = x1)`: `f[i] ← (f[i] ± g[i]) mod q`,
  four coefficients at a time.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

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

/-- The 128 entries of `T` as `u32`s at `[b]`, through `x9`. -/
def table (T : List Nat) (b : Reg) : List Instr :=
  (List.range 128).flatMap fun k =>
    [.movz .x .x9 (BitVec.ofNat 16 (T.getD k 0)) 0, .str .w .x9 b (4 * k)]

/-! ## Vectors

`multiplyNTTs`, `add` and `sub` compute on four coefficients at a time, in the
32-bit lanes of AdvSIMD registers, with `q` in the lanes of `v16` and
`M = ⌊2³¹ / q⌋ = 645083` in those of `v17`. A product `x < 2³¹` of two
coefficients is reduced with `sqdmulh` by `M`, which gives
`t = ⌊x · M / 2³¹⌋`, `⌊x / q⌋` or one less, so that `x - t · q` (`mls`) is
less than `2q`; a lane `d < 2q` is reduced to `min(d, d - q)` (`umin`), as
`d - q` wraps around when `d < q`. -/

/-- `q` in `x9` and in the lanes of `v16`; `M` in `x10` and in those of `v17`. -/
def vconsts : List Instr :=
  .movz .x .x9 3329 0 :: movImm .x10 645083 ++ [.vop (.dup .s4 .v16 .x9), .vop (.dup .s4 .v17 .x10)]

/-- `d ← d mod q` for lanes less than `2q`, with a temporary `t`. -/
def vcsub (d t : VReg) : List Instr := [.vop (.sub .s4 t d .v16), .vop (.umin d d t)]

/-! ## `add` and `sub` -/

/-- `v2 ← (v0 + v1) mod q`: `min(a + b, a + b - q)`. -/
def vaddOp : List Instr := .vop (.add .s4 .v2 .v0 .v1) :: vcsub .v2 .v3

/-- `v2 ← (v0 - v1) mod q`: `min(a - b, a - b + q)`, as `a - b` wraps around
when `a < b`. -/
def vsubOp : List Instr :=
  [.vop (.sub .s4 .v2 .v0 .v1), .vop (.add .s4 .v3 .v2 .v16), .vop (.umin .v2 .v2 .v3)]

/-- Four coefficients: `v0 = f[4k..]`, `v1 = g[4k..]`, `op`, `f[4k..] ← v2`,
and on to the next four. -/
def vmapBody (op : List Instr) : List Instr :=
  [.ldrq .v0 .x0 0, .ldrq .v1 .x1 0] ++ op ++
    [.strq .v2 .x0 0, .addImm .x .x0 .x0 16, .addImm .x .x1 .x1 16, .subImm .x .x10 .x10 1]

/-- `op` on the 256 coefficients, four at a time, with `q` in the lanes of
`v16`. -/
def vmapLoop (op : List Instr) : Prog isa :=
  .seq (.block [.movz .x .x9 3329 0, .vop (.dup .s4 .v16 .x9), .movz .x .x10 64 0])
    (.loop (.block (vmapBody op)) (.nonzero .x .x10))

/-- `add(f = x0, g = x1)`: `f[i] ← (f[i] + g[i]) mod q`. -/
def add : Prog isa := vmapLoop vaddOp

/-- `sub(f = x0, g = x1)`: `f[i] ← (f[i] - g[i]) mod q`. -/
def sub : Prog isa := vmapLoop vsubOp

/-! ## `multiplyNTTs` -/

/-- Four pairs `i = 4c … 4c + 3`: `f` in `v0`, `v1` and `g` in `v4`, `v5`
(`[x1]`, `[x2]`), the `γᵢ` in `v18` (`[x3]`); their even and odd
coefficients gathered (`uzp1`, `uzp2`) into `v6`, `v7` (`f`) and `v19`,
`v20` (`g`); `r = f[2i+1] g[2i+1]`, reduced to less than `2q`;
`h[2i] = f[2i] g[2i] + r γᵢ` (`v23`) and `h[2i+1] = f[2i] g[2i+1] +
f[2i+1] g[2i]` (`v24`), each less than `3q² < 2³¹` and reduced; and back in
order (`zip1`, `zip2`) to `[x0]`. -/
def vmulBody : List Instr :=
  [.ldrq .v0 .x1 0, .ldrq .v1 .x1 16, .ldrq .v4 .x2 0, .ldrq .v5 .x2 16, .ldrq .v18 .x3 0,
    .vop (.perm .uzp1 .s4 .v6 .v0 .v1), .vop (.perm .uzp2 .s4 .v7 .v0 .v1),
    .vop (.perm .uzp1 .s4 .v19 .v4 .v5), .vop (.perm .uzp2 .s4 .v20 .v4 .v5),
    .vop (.mul .v21 .v7 .v20), .vop (.sqdmulh .v22 .v21 .v17), .vop (.mls .v21 .v22 .v16),
    .vop (.mul .v23 .v6 .v19), .vop (.mla .v23 .v21 .v18), .vop (.sqdmulh .v22 .v23 .v17),
    .vop (.mls .v23 .v22 .v16)] ++ vcsub .v23 .v22 ++
  [.vop (.mul .v24 .v6 .v20), .vop (.mla .v24 .v7 .v19), .vop (.sqdmulh .v22 .v24 .v17),
    .vop (.mls .v24 .v22 .v16)] ++ vcsub .v24 .v22 ++
  [.vop (.perm .zip1 .s4 .v0 .v23 .v24), .vop (.perm .zip2 .s4 .v1 .v23 .v24), .strq .v0 .x0 0,
    .strq .v1 .x0 16, .addImm .x .x0 .x0 32, .addImm .x .x1 .x1 32, .addImm .x .x2 .x2 32,
    .addImm .x .x3 .x3 16, .subImm .x .x11 .x11 1]

def multiplyNTTs : Prog isa :=
  .seq (.block (table gammaTable .x3 ++ vconsts ++ [.movz .x .x11 32 0]))
    (.loop (.block vmulBody) (.nonzero .x .x11))

end VG.Impl.MlKem.AArch64
