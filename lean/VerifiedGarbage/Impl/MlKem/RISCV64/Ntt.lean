module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Poly

/-!
# ML-KEM on RISC-V: the NTT, its inverse and `MultiplyNTTs`

As on PPC64LE (`Impl/MlKem/PPC64LE/Ntt.lean`): the products of two
coefficients (less than `q² < 2²⁴`), and the sums of two of them in
`MultiplyNTTs` (less than `2q² < 2²⁵`), are reduced by `reduce`: the Barrett
reduction `barrett32` (`VG.Proof.MlKem.barrett32`),
`x - ⌊(x >> 11) · 161270 / 2¹⁸⌋ · q`, leaves a value less than `2q`
congruent to `x`, and a subtraction of `q` and a `fixup` finish it.
`a5 = 161270` and `a6 = q` throughout (`consts`).

Multiplications are what the code counts: the product of the quotient by
`q = 2¹¹ + 2¹⁰ + 2⁸ + 1` is four subtractions of shifts (`subMulQ`), and
`fixup` needs none, so a butterfly multiplies twice (the product and the
quotient's estimate) and a pair of `MultiplyNTTs` eight times.

The tables of `ζ^BitRev7(k)` (`zetaTable`) and of the `γᵢ` of
`MultiplyNTTs` (`gammaTable`) are stored in the first 512 bytes of
`scratch`, as 128 `u32`s (`table`: each entry an `addi` of `t0 = 2048`,
then a store, through `t2`), and read in order through a pointer. The
functions use only registers the calling convention lets them clobber,
make no calls and use no stack.

* `vg_mlkem_ntt(f = a0, scratch = a1)`: the seven layers of Algorithm 9 as
  three nested loops, with `a0 = f + 1024` (the end of `f`),
  `a7 = 4 len` (from 512, halved, until it is 4), `a1` the next zeta of the
  table (from `zetas[1]`); for each block, its zeta in `a4`, and `len`
  butterflies on `a2 = f + 4j` and `a3 = f + 4(j + len)`, counted by `t1`;
  the next block starts where the butterflies left `a3`, until `a2 = a0`.
* `vg_mlkem_inv_ntt(f = a0, scratch = a1)`: the same for Algorithm 10, with
  `a7` from 8 (doubled, until it is 1024), the zetas from `zetas[127]`
  down, and the inverse butterflies; then every coefficient times 3303.
* `vg_mlkem_multiply_ntts(h = a0, f = a1, g = a2, scratch = a3)`: for each
  pair `i` (counted by `t1`), `h[2i] = f[2i] g[2i] + (f[2i+1] g[2i+1] mod q) γᵢ`
  and `h[2i+1] = f[2i] g[2i+1] + f[2i+1] g[2i]`, each reduced, with `γᵢ`
  read through `a3`.

A butterfly stores `f[j + len]` before `f[j]`, and an inverse butterfly
`f[j]` before `f[j + len]`, the order in which Algorithms 9 and 10 write
them. Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.RISCV64

open VG.RISCV64

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

/-- `d ← d - t · q`, as `q = 2¹¹ + 2¹⁰ + 2⁸ + 1`, with `u` a temporary. -/
def subMulQ (d t u : Reg) : List Instr :=
  [.sub d d t, .shift .sll .d u t 8, .sub d d u, .shift .sll .d u t 10, .sub d d u,
    .shift .sll .d u t 11, .sub d d u]

/-- `d ← d - ⌊(d >> 11) · 161270 / 2¹⁸⌋ · q`, with `161270` in `a5` and `t`
and `u` temporaries. -/
def barrett (d t u : Reg) : List Instr :=
  [.shift .srl .d t d 11, .mul t t .a5, .shift .srl .d t t 18] ++ subMulQ d t u

/-- `d ← d mod q` for `d < 2²⁵`, with `q` in `a6` and `t` and `u`
temporaries. -/
def reduce (d t u : Reg) : List Instr := barrett d t u ++ [.sub d d .a6] ++ fixup d t .a6

/-- `a5 = 161270 = 0x27000 + 1526`, `a6 = q`. -/
def consts : List Instr := [.lui .a5 0x27, .addi .a5 .a5 1526] ++ liq .a6 3329

/-- The 128 entries of `T` (each below 3328) as `u32`s at `[b]`, each
`t0 + (T[k] - 2048)` with `t0 = 2048`, through `t2`. -/
def table (T : List Nat) (b : Reg) : List Instr :=
  [.lui .t0 1, .addi .t0 .t0 (-2048)] ++
  (List.range 128).flatMap fun k => [.addi .t2 .t0 ((T.getD k 0 : Int) - 2048), .store .w .t2 b (4 * k)]

/-! ## `ntt` -/

/-- The butterfly on `[a2]` and `[a3]` with the zeta `a4`: `t = ζ·f[j + len]`
in `t0`, then `f[j + len] = f[j] - t` and `f[j] = f[j] + t`. -/
def bflyBody : List Instr :=
  [.load .w .t2 .a2 0, .load .w .t0 .a3 0, .mul .t0 .a4 .t0] ++ reduce .t0 .t3 .t5 ++
  [.sub .t3 .t2 .t0] ++ fixup .t3 .t4 .a6 ++ [.store .w .t3 .a3 0, .add .t2 .t2 .t0,
    .sub .t2 .t2 .a6] ++ fixup .t2 .t4 .a6 ++
  [.store .w .t2 .a2 0, .addi .a2 .a2 4, .addi .a3 .a3 4, .addi .t1 .t1 (-1)]

/-- A block: its zeta, then `len` butterflies. -/
def nttBlockCode : Prog isa :=
  .seq (.block [.load .w .a4 .a1 0, .addi .a1 .a1 4, .add .a3 .a2 .a7, .shift .srl .d .t1 .a7 2])
    (.seq (.loop (.block bflyBody) (.nonzero .t1))
      (.block [.addi .a2 .a3 0, .sub .t0 .a2 .a0]))

/-- A layer: its blocks. -/
def nttLayerCode : Prog isa :=
  .seq (.block [.addi .a2 .a0 (-1024)])
    (.seq (.loop nttBlockCode (.nonzero .t0))
      (.block [.shift .srl .d .a7 .a7 1, .addi .t0 .a7 (-4)]))

def ntt : Prog isa :=
  .seq (.block (table zetaTable .a1 ++ consts ++
      ([.addi .a0 .a0 1024, .addi .a1 .a1 4, .li .a7 512] : List Instr)))
    (.loop nttLayerCode (.nonzero .t0))

/-! ## `nttInv` -/

/-- The inverse butterfly on `[a2]` and `[a3]` with the zeta `a4`:
`f[j] = f[j] + f[j + len]`, then `f[j + len] = ζ·(f[j + len] - f[j])`. -/
def ibflyBody : List Instr :=
  [.load .w .t2 .a2 0, .load .w .t0 .a3 0, .add .t3 .t2 .t0, .sub .t3 .t3 .a6] ++
  fixup .t3 .t4 .a6 ++ [.store .w .t3 .a2 0, .sub .t0 .t0 .t2] ++ fixup .t0 .t4 .a6 ++
  [.mul .t0 .a4 .t0] ++ reduce .t0 .t3 .t5 ++
  [.store .w .t0 .a3 0, .addi .a2 .a2 4, .addi .a3 .a3 4, .addi .t1 .t1 (-1)]

/-- A block: its zeta, then `len` inverse butterflies. -/
def nttInvBlockCode : Prog isa :=
  .seq (.block [.load .w .a4 .a1 0, .addi .a1 .a1 (-4), .add .a3 .a2 .a7, .shift .srl .d .t1 .a7 2])
    (.seq (.loop (.block ibflyBody) (.nonzero .t1))
      (.block [.addi .a2 .a3 0, .sub .t0 .a2 .a0]))

/-- A layer: its blocks. -/
def nttInvLayerCode : Prog isa :=
  .seq (.block [.addi .a2 .a0 (-1024)])
    (.seq (.loop nttInvBlockCode (.nonzero .t0))
      (.block [.shift .sll .d .a7 .a7 1, .addi .t0 .a7 (-1024)]))

/-- `[a2] ← [a2] · a4 mod q`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  [.load .w .t2 .a2 0, .mul .t2 .t2 .a4] ++ reduce .t2 .t3 .t5 ++
  [.store .w .t2 .a2 0, .addi .a2 .a2 4, .addi .t1 .t1 (-1)]

def nttInv : Prog isa :=
  .seq (.block (table zetaTable .a1 ++ consts ++
      ([.addi .a0 .a0 1024, .addi .a1 .a1 508, .li .a7 8] : List Instr)))
    (.seq (.loop nttInvLayerCode (.nonzero .t0))
    (.seq (.block (liq .a4 3303 ++ ([.addi .a2 .a0 (-1024), .li .t1 256] : List Instr)))
      (.loop (.block scaleBody) (.nonzero .t1))))

/-! ## `multiplyNTTs` -/

/-- The pair `i`: `a4 = f[2i]`, `t2 = f[2i+1]`, `t3 = g[2i]`,
`t4 = g[2i+1]`, the sums in `t0`, `γᵢ` and the products in `a7`. -/
def mulBody : List Instr :=
  [.load .w .a4 .a1 0, .load .w .t2 .a1 4, .load .w .t3 .a2 0, .load .w .t4 .a2 4,
   .mul .t0 .t2 .t4] ++ reduce .t0 .a7 .t5 ++
  [.load .w .a7 .a3 0, .mul .t0 .t0 .a7, .mul .a7 .a4 .t3, .add .t0 .a7 .t0] ++
  reduce .t0 .a7 .t5 ++
  [.store .w .t0 .a0 0, .mul .t0 .a4 .t4, .mul .a7 .t2 .t3, .add .t0 .t0 .a7] ++
  reduce .t0 .a7 .t5 ++
  [.store .w .t0 .a0 4, .addi .a0 .a0 8, .addi .a1 .a1 8, .addi .a2 .a2 8, .addi .a3 .a3 4,
   .addi .t1 .t1 (-1)]

def multiplyNTTs : Prog isa :=
  .seq (.block (table gammaTable .a3 ++ consts ++ ([.li .t1 128] : List Instr)))
    (.loop (.block mulBody) (.nonzero .t1))

end VG.Impl.MlKem.RISCV64
