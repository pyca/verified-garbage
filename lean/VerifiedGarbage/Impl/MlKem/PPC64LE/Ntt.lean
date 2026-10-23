module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Poly

/-!
# ML-KEM on PPC64LE: the NTT, its inverse and `MultiplyNTTs`

As on 32-bit ARM (`Impl/MlKem/Arm/Ntt.lean`), with 64-bit registers: the
products of two coefficients (less than `q² < 2²⁴`), and the sums of two of
them in `MultiplyNTTs` (less than `2q² < 2²⁵`), are reduced by `reduce`: the
Barrett reduction `barrett32` (`VG.Proof.MlKem.barrett32`),
`x - ⌊(x >> 11) · 161270 / 2¹⁸⌋ · q`, leaves a value less than `2q`
congruent to `x`, and a subtraction of `q` and a `fixup` finish it.
`r8 = 161270` and `r9 = q` throughout (`consts`).

The tables of `ζ^BitRev7(k)` (`zetaTable`) and of the `γᵢ` of
`MultiplyNTTs` (`gammaTable`) are stored in the first 512 bytes of
`scratch`, as 128 `u32`s (`table`, through `r12`), and read in order
through a pointer. The functions use `r14` and `r15`, which they save in
`scratch[512..528)` and restore; they make no calls, so the link register is
never written, and they use no stack.

* `vg_mlkem_ntt(f = r3, scratch = r4)`: the seven layers of Algorithm 9 as
  three nested loops, with `r3 = f + 1024` (the end of `f`),
  `r10 = 4 len` (from 512, halved, until it is 4), `r4` the next zeta of the
  table (from `zetas[1]`); for each block, its zeta in `r7`, and `len`
  butterflies on `r5 = f + 4j` and `r6 = f + 4(j + len)`, counted by `r11`;
  the next block starts where the butterflies left `r6`, until `r5 = r3`.
* `vg_mlkem_inv_ntt(f = r3, scratch = r4)`: the same for Algorithm 10, with
  `r10` from 8 (doubled, until it is 1024), the zetas from `zetas[127]`
  down, and the inverse butterflies; then every coefficient times 3303.
* `vg_mlkem_multiply_ntts(h = r3, f = r4, g = r5, scratch = r6)`: for each
  pair `i` (counted by `r11`), `h[2i] = f[2i] g[2i] + (f[2i+1] g[2i+1] mod q) γᵢ`
  and `h[2i+1] = f[2i] g[2i+1] + f[2i+1] g[2i]`, each reduced, with `γᵢ`
  read through `r6`.

A butterfly stores `f[j + len]` before `f[j]`, and an inverse butterfly
`f[j]` before `f[j + len]`, the order in which Algorithms 9 and 10 write
them. Every address and branch depends only on the pointers.
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

/-! ## `ntt` -/

/-- The butterfly on `[r5]` and `[r6]` with the zeta `r7`: `t = ζ·f[j + len]`
in `r0`, then `f[j + len] = f[j] - t` and `f[j] = f[j] + t`. -/
def bflyBody : List Instr :=
  [.load .w .r12 .r5 0, .load .w .r0 .r6 0, .mul .r0 .r7 .r0] ++ reduce .r0 .r14 ++
  [.sub .r14 .r12 .r0] ++ fixup .r14 .r15 .r9 ++ [.store .w .r14 .r6 0, .add .r12 .r12 .r0,
    .sub .r12 .r12 .r9] ++ fixup .r12 .r15 .r9 ++
  [.store .w .r12 .r5 0, .addi .r5 .r5 4, .addi .r6 .r6 4, .subi .r11 .r11 1]

/-- A block: its zeta, then `len` butterflies. -/
def nttBlockCode : Prog isa :=
  .seq (.block [.load .w .r7 .r4 0, .addi .r4 .r4 4, .add .r6 .r5 .r10, .lsr .d .r11 .r10 2])
    (.seq (.loop (.block bflyBody) (.nonzero .d .r11))
      (.block [.addi .r5 .r6 0, .sub .r0 .r5 .r3]))

/-- A layer: its blocks. -/
def nttLayerCode : Prog isa :=
  .seq (.block [.subi .r5 .r3 1024])
    (.seq (.loop nttBlockCode (.nonzero .d .r0)) (.block [.lsr .d .r10 .r10 1, .subi .r0 .r10 4]))

def ntt : Prog isa :=
  .seq (.block (saveRegs .r4 512 ++ table zetaTable .r4 ++ consts ++
      ([.addi .r3 .r3 1024, .addi .r4 .r4 4, .li .r10 512] : List Instr)))
    (.seq (.loop nttLayerCode (.nonzero .d .r0)) (.block (restoreRegs .r4 0)))

/-! ## `nttInv` -/

/-- The inverse butterfly on `[r5]` and `[r6]` with the zeta `r7`:
`f[j] = f[j] + f[j + len]`, then `f[j + len] = ζ·(f[j + len] - f[j])`. -/
def ibflyBody : List Instr :=
  [.load .w .r12 .r5 0, .load .w .r0 .r6 0, .add .r14 .r12 .r0, .sub .r14 .r14 .r9] ++
  fixup .r14 .r15 .r9 ++ [.store .w .r14 .r5 0, .sub .r0 .r0 .r12] ++ fixup .r0 .r15 .r9 ++
  [.mul .r0 .r7 .r0] ++ reduce .r0 .r14 ++
  [.store .w .r0 .r6 0, .addi .r5 .r5 4, .addi .r6 .r6 4, .subi .r11 .r11 1]

/-- A block: its zeta, then `len` inverse butterflies. -/
def nttInvBlockCode : Prog isa :=
  .seq (.block [.load .w .r7 .r4 0, .subi .r4 .r4 4, .add .r6 .r5 .r10, .lsr .d .r11 .r10 2])
    (.seq (.loop (.block ibflyBody) (.nonzero .d .r11))
      (.block [.addi .r5 .r6 0, .sub .r0 .r5 .r3]))

/-- A layer: its blocks. -/
def nttInvLayerCode : Prog isa :=
  .seq (.block [.subi .r5 .r3 1024])
    (.seq (.loop nttInvBlockCode (.nonzero .d .r0))
      (.block [.lsl .r10 .r10 1, .subi .r0 .r10 1024]))

/-- `[r5] ← [r5] · r7 mod q`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  [.load .w .r12 .r5 0, .mul .r12 .r12 .r7] ++ reduce .r12 .r14 ++
  [.store .w .r12 .r5 0, .addi .r5 .r5 4, .subi .r11 .r11 1]

def nttInv : Prog isa :=
  .seq (.block (saveRegs .r4 512 ++ table zetaTable .r4 ++ consts ++
      ([.addi .r3 .r3 1024, .addi .r4 .r4 508, .li .r10 8] : List Instr)))
    (.seq (.loop nttInvLayerCode (.nonzero .d .r0))
    (.seq (.block [.li .r7 3303, .subi .r5 .r3 1024, .li .r11 256])
    (.seq (.loop (.block scaleBody) (.nonzero .d .r11)) (.block (restoreRegs .r4 512)))))

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
