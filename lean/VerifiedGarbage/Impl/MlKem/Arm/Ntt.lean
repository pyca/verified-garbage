module

public import VerifiedGarbage.Impl.MlKem.Arm.Poly

/-!
# ML-KEM on 32-bit ARM: the NTT, its inverse and `MultiplyNTTs`

`-q` is in a register (`r8` in the transforms, `r12` in `MultiplyNTTs`), so
that a subtraction of a multiple of `q` is an `mla`.

A product by a zeta `z` is reduced with the zeta's quotient
`zp = ⌊2¹⁶ z / q⌋` (`zetaQuot`): for `b < 2¹⁶`, `⌊b · zp / 2¹⁶⌋` is
`⌊b z / q⌋` or one less, so `b z - ⌊b · zp / 2¹⁶⌋ · q` (`mulz`: two `mul`s, a
shift and an `mla`) is less than `2q` and congruent to `b z`. The table of
the transforms holds each zeta with its quotient in one word,
`zp + 2¹⁶ z` (`tableZ`, in the first 512 bytes of `scratch`, as 128 `u32`s,
through `r12`), which a block unpacks into `r7` and `r9` (`zetaLoad`).

The butterflies are lazy: they reduce only the product, and the
coefficients between layers are words congruent to the specification's.

* `vg_mlkem_ntt(f = r0, scratch = r1)`: the seven layers of Algorithm 9 as
  three nested loops, with `r0 = f + 1024` (the end of `f`), `r10 = 4 len`
  (from 512, halved, until it is 4), `r1` the next zeta of the table (from
  `zetas[1]`); for each block, its zeta in `r7` and `r9`, and `len`
  butterflies on `r2 = f + 4j` and `r3 = f + 4(j + len)`, counted by `r11`;
  the next block starts where the butterflies left `r3`, until `r2 = r0`.
  A butterfly stores `f[j] + 2q - t` and `f[j] + t` for the product `t`
  (`2q` in `r12`): a layer adds less than `2q` to the coefficients, which
  stay less than `15q < 2¹⁶`. A last loop reduces them (`canonBody`): for
  `v < 15q`, `⌊v · 40318 / 2²⁷⌋` is `⌊v / q⌋`.
* `vg_mlkem_inv_ntt(f = r0, scratch = r1)`: the same for Algorithm 10, with
  `r10` from 8 (doubled, until it is 1024) and the zetas from `zetas[127]`
  down. A butterfly stores `x - ⌊x / 2¹²⌋ · q` for the sum `x` (less than
  `2q` for a sum less than `4q`, as `2¹² - q = 767`), and the product of
  the zeta and `f[j + len] + 2q - f[j]`: the coefficients stay less than
  `2q`. Then every coefficient times 3303, reduced (`csub`, with `q` in
  `r12`).
* `vg_mlkem_multiply_ntts(h = r0, f = r1, g = r2, scratch = r3)`: for each
  pair `i` (counted by `r11`), `h[2i] = f[2i] g[2i] + (f[2i+1] g[2i+1] mod q) γᵢ`
  and `h[2i+1] = f[2i] g[2i+1] + f[2i+1] g[2i]`, each reduced, with `γᵢ`
  read through `r3` (`gammaTable`, stored by `table`). The products of two
  coefficients (less than `q²`) and the sums (less than `3q² < 2²⁵`) are
  reduced with the Barrett reduction `barrett32`
  (`VG.Proof.MlKem.barrett32`), `x - ⌊(x >> 11) · 161270 / 2¹⁸⌋ · q`, which
  leaves a value less than `2q` congruent to `x` (`barrett`, with `161270`
  in `r8`), and a conditional subtraction of `q` (`csubN`).

The functions use `r4`–`r11`, which they save in `scratch[512..544)` and
restore (`saveRegs`, `restoreRegs`); they make no calls, so `lr` is never
written, and they use no stack. A butterfly stores `f[j + len]` before
`f[j]`, and an inverse butterfly `f[j]` before `f[j + len]`, the order in
which Algorithms 9 and 10 write them. Every address and branch depends only
on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.Arm

open VG.Arm

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

/-- `⌊2¹⁶ z / q⌋`: the quotient of a zeta. -/
def zetaQuot (z : Nat) : Nat := z * 65536 / 3329

/-- `d ← d - ⌊(d >> 11) · 161270 / 2¹⁸⌋ · q`, with `161270` in `c`, `-q` in
`N` and `t` a temporary. -/
def barrett (d t c N : Reg) : List Instr :=
  [.mov t (.shifted d .lsr 11), .mul t t c, .mov t (.shifted t .lsr 18), .mla d t N d]

/-- `d ← d - q` unless that is negative: `d mod q` for `d < 2q`, with `-q` in
`N` and `t` a temporary, which becomes the sign bit of `d - q + 2³¹`: 1 if
`d ≥ q`. -/
def csubN (d t N : Reg) : List Instr :=
  [.dp .add t d (.reg N), .dp .add t t (.imm 0x80000000), .mov t (.shifted t .lsr 31), .mla d t N d]

/-- `d ← d - q`, plus `q` if that is negative: `d mod q` for `d < 2q`, with
`q` in `Q` and `t` a temporary. -/
def csub (d t Q : Reg) : List Instr := [.dp .sub d d (.reg Q), .mov t (.shifted d .lsr 31), .mla d t Q d]

/-- `d ← d mod q` for `d < 2²⁵`, with `161270` in `c`, `-q` in `N` and `t` a
temporary. -/
def reduce (d t c N : Reg) : List Instr := barrett d t c N ++ csubN d t N

/-- `acc ← acc · z - ⌊acc · zp / 2¹⁶⌋ · q`, with `-q` in `N` and `t` a
temporary: less than `2q` and congruent to `acc · z`, for `acc < 2¹⁶`. -/
def mulz (acc t z zp N : Reg) : List Instr :=
  [.mul t acc zp, .mov t (.shifted t .lsr 16), .mul acc acc z, .mla acc t N acc]

/-- `r8 = 161270`. -/
def consts : List Instr := [.movw .r8 0x75F6, .movt .r8 0x2]

/-- The 128 entries of `T` as `u32`s at `[b]`, through `r12`. -/
def table (T : List Nat) (b : Reg) : List Instr :=
  (List.range 128).flatMap fun k => [.movw .r12 (BitVec.ofNat 16 (T.getD k 0)), .str .r12 b (4 * k)]

/-- The 128 entries of `T`, each with its quotient, `zp + 2¹⁶ z`, as `u32`s
at `[b]`, through `r12`. -/
def tableZ (T : List Nat) (b : Reg) : List Instr :=
  (List.range 128).flatMap fun k =>
    [.movw .r12 (BitVec.ofNat 16 (zetaQuot (T.getD k 0))), .movt .r12 (BitVec.ofNat 16 (T.getD k 0)),
     .str .r12 b (4 * k)]

/-- The zeta at `r1` to `r7`, and its quotient to `r9`. -/
def zetaLoad : List Instr :=
  [.ldr .r9 .r1 0, .mov .r7 (.shifted .r9 .lsr 16), .dp .sub .r9 .r9 (.shifted .r7 .lsl 16)]

/-- `r8 = -q = 0xFFFFF2FF`, `r12 = 2q`. -/
def constsN : List Instr := [.movw .r8 0xF2FF, .movt .r8 0xFFFF, .movw .r12 6658]

/-- The callee-saved registers we use. -/
def savedRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- Our caller's `r4`–`r11` stored at `[b, #off]`. -/
def saveRegs (b : Reg) (off : Nat) : List Instr :=
  (List.range 8).flatMap fun i => [.str (savedRegs.getD i .r4) b (off + 4 * i)]

/-- Our caller's `r4`–`r11` loaded from `[b, #off]`. -/
def restoreRegs (b : Reg) (off : Nat) : List Instr :=
  (List.range 8).flatMap fun i => [.ldr (savedRegs.getD i .r4) b (off + 4 * i)]

/-! ## `ntt` -/

/-- The butterfly on `[r2]` and `[r3]` with the zeta in `r7` and `r9`:
`t = ζ·f[j + len]` less a multiple of `q` in `r5`, then
`f[j + len] = f[j] + 2q - t` and `f[j] = f[j] + t`. -/
def bflyBody : List Instr :=
  ([.ldr .r5 .r3 0] : List Instr) ++ mulz .r5 .r6 .r7 .r9 .r8 ++
  [.ldr .r4 .r2 0, .dp .add .r6 .r4 (.reg .r5), .dp .add .r4 .r4 (.reg .r12), .dp .sub .r4 .r4 (.reg .r5),
   .str .r4 .r3 0, .str .r6 .r2 0, .dp .add .r2 .r2 (.imm 4), .dp .add .r3 .r3 (.imm 4),
   .subs .r11 .r11 (.imm 1)]

/-- A block: its zeta, then `len` butterflies. -/
def nttBlockCode : Prog isa :=
  .seq (.block (zetaLoad ++ ([.dp .add .r1 .r1 (.imm 4), .dp .add .r3 .r2 (.reg .r10),
      .mov .r11 (.shifted .r10 .lsr 2)] : List Instr)))
    (.seq (.loop (.block bflyBody) .ne) (.block [.mov .r2 (.reg .r3), .cmp .r2 (.reg .r0)]))

/-- A layer: its blocks. -/
def nttLayerCode : Prog isa :=
  .seq (.block [.dp .sub .r2 .r0 (.imm 1024)])
    (.seq (.loop nttBlockCode .ne) (.block [.mov .r10 (.shifted .r10 .lsr 1), .cmp .r10 (.imm 4)]))

/-- `[r2] ← [r2] mod q`, for a coefficient less than `15q`, with `40318` in
`r9`, and on to the next. -/
def canonBody : List Instr :=
  [.ldr .r4 .r2 0, .mul .r6 .r4 .r9, .mov .r6 (.shifted .r6 .lsr 27), .mla .r4 .r6 .r8 .r4, .str .r4 .r2 0,
   .dp .add .r2 .r2 (.imm 4), .subs .r11 .r11 (.imm 1)]

def ntt : Prog isa :=
  .seq (.block (saveRegs .r1 512 ++ tableZ zetaTable .r1 ++ constsN ++
      ([.dp .add .r0 .r0 (.imm 1024), .dp .add .r1 .r1 (.imm 4), .mov .r10 (.imm 512)] : List Instr)))
    (.seq (.loop nttLayerCode .ne)
    (.seq (.block [.movw .r9 40318, .dp .sub .r2 .r0 (.imm 1024), .mov .r11 (.imm 256)])
    (.seq (.loop (.block canonBody) .ne) (.block (restoreRegs .r1 0)))))

/-! ## `nttInv` -/

/-- The inverse butterfly on `[r2]` and `[r3]` with the zeta in `r7` and
`r9`: `f[j] = f[j] + f[j + len]`, less a multiple of `q`, then
`f[j + len] = ζ·(f[j + len] + 2q - f[j])`. -/
def ibflyBody : List Instr :=
  ([.ldr .r4 .r2 0, .ldr .r5 .r3 0, .dp .add .r6 .r4 (.reg .r5), .dp .add .r5 .r5 (.reg .r12),
    .dp .sub .r5 .r5 (.reg .r4), .mov .r4 (.shifted .r6 .lsr 12), .mla .r6 .r4 .r8 .r6,
    .str .r6 .r2 0] : List Instr) ++ mulz .r5 .r4 .r7 .r9 .r8 ++
  [.str .r5 .r3 0, .dp .add .r2 .r2 (.imm 4), .dp .add .r3 .r3 (.imm 4), .subs .r11 .r11 (.imm 1)]

/-- A block: its zeta, then `len` inverse butterflies. -/
def nttInvBlockCode : Prog isa :=
  .seq (.block (zetaLoad ++ ([.dp .sub .r1 .r1 (.imm 4), .dp .add .r3 .r2 (.reg .r10),
      .mov .r11 (.shifted .r10 .lsr 2)] : List Instr)))
    (.seq (.loop (.block ibflyBody) .ne) (.block [.mov .r2 (.reg .r3), .cmp .r2 (.reg .r0)]))

/-- A layer: its blocks. -/
def nttInvLayerCode : Prog isa :=
  .seq (.block [.dp .sub .r2 .r0 (.imm 1024)])
    (.seq (.loop nttInvBlockCode .ne)
      (.block [.mov .r10 (.shifted .r10 .lsl 1), .cmp .r10 (.imm 1024)]))

/-- `[r2] ← [r2] · 3303 mod q`, for the zeta in `r7` and `r9` and `q` in
`r12`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  ([.ldr .r4 .r2 0] : List Instr) ++ mulz .r4 .r6 .r7 .r9 .r8 ++ csub .r4 .r6 .r12 ++
  [.str .r4 .r2 0, .dp .add .r2 .r2 (.imm 4), .subs .r11 .r11 (.imm 1)]

/-- `3303` and its quotient `65024` in `r7` and `r9`, `q` in `r12`, and the
pointer and the count. -/
def scalePre : List Instr :=
  [.movw .r7 3303, .movw .r9 65024, .movw .r12 3329, .dp .sub .r2 .r0 (.imm 1024), .mov .r11 (.imm 256)]

def nttInv : Prog isa :=
  .seq (.block (saveRegs .r1 512 ++ tableZ zetaTable .r1 ++ constsN ++
      ([.dp .add .r0 .r0 (.imm 1024), .dp .add .r1 .r1 (.imm 508), .mov .r10 (.imm 8)] : List Instr)))
    (.seq (.loop nttInvLayerCode .ne)
    (.seq (.block scalePre)
    (.seq (.loop (.block scaleBody) .ne) (.block (restoreRegs .r1 512)))))

/-! ## `multiplyNTTs` -/

/-- The pair `i`: `r4 = f[2i]`, `r5 = f[2i+1]`, `r6 = g[2i]`, `r7 = g[2i+1]`,
the sums in `r9`, `γᵢ` and the quotients in `r10`. -/
def mulBody : List Instr :=
  ([.ldr .r5 .r1 4, .ldr .r7 .r2 4, .mul .r9 .r5 .r7] : List Instr) ++ barrett .r9 .r10 .r8 .r12 ++
  [.ldr .r10 .r3 0, .mul .r9 .r9 .r10, .ldr .r4 .r1 0, .ldr .r6 .r2 0, .mla .r9 .r4 .r6 .r9] ++
  reduce .r9 .r10 .r8 .r12 ++
  [.str .r9 .r0 0, .mul .r9 .r4 .r7, .mla .r9 .r5 .r6 .r9] ++
  reduce .r9 .r10 .r8 .r12 ++
  [.str .r9 .r0 4, .dp .add .r0 .r0 (.imm 8), .dp .add .r1 .r1 (.imm 8), .dp .add .r2 .r2 (.imm 8),
   .dp .add .r3 .r3 (.imm 4), .subs .r11 .r11 (.imm 1)]

def multiplyNTTs : Prog isa :=
  .seq (.block (saveRegs .r3 512 ++ table gammaTable .r3 ++ consts ++
      ([.movw .r12 0xF2FF, .movt .r12 0xFFFF, .mov .r11 (.imm 128)] : List Instr)))
    (.seq (.loop (.block mulBody) .ne) (.block (restoreRegs .r3 0)))

end VG.Impl.MlKem.Arm
