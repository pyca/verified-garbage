module

public import VerifiedGarbage.Impl.MlKem.X86.Vec

/-!
# ML-KEM on x86 (32-bit): the NTT, its inverse and `MultiplyNTTs`

## `ntt(f, scratch)` and `nttInv(f, scratch)` (Algorithms 9 and 10)

Eight butterflies at a time, on the 16-bit words of XMM registers, with the
pieces of `Impl/MlKem/X86/Vec.lean`, inside the MCDT frame `pmullw` and
`pmulhw` need (`wframe`); the functions use only `eax`, `ecx`, `edx` and the
XMM registers, and their arguments are at `[esp + 20]` and `[esp + 24]`
there. `scratch` holds

* a table of the 128 zetas in Montgomery form (times `2¹⁶ mod q`), as
  words, in its first 256 bytes (`wtable`, two entries a store through
  `edx`), which `edx` moves up from entry 1 (for `nttInv` the table,
  `montZetasRev`, is in the order of use);
* the 256 coefficients as words, in its last 512 bytes: `wpackPass` copies
  them there from the `u32`s of `f` (`packssdw`), the layers work on them,
  and `wunpackPass` copies them back (for `nttInv`, each times
  `3303 = 128⁻¹ mod q`, `scaleCore`).

The end of the words, `scratch + 1024`, is stored in the argument slot of
`scratch`, which the loops compare `eax` with (`nttTable`).

Every coefficient stays in `[0, q)`: a butterfly of `ntt` (`fCore`) leaves
`a + t mod q` and `a - t mod q` for `t`, the Montgomery product of `b` and
the zeta, and one of `nttInv` (`iCore`) `a + b mod q` and the Montgomery
product of `b - a` and the zeta (`wmont`, `wcadd`, `wcsub`).

* A layer with `len ≥ 8` (`layer8`) is a loop over its blocks, each a loop
  over its groups of eight butterflies (`lBody`): `eax` points at
  coefficient `j`, `[eax + 2 · len]` is coefficient `j + len`, the zeta of
  the block is in every word of `xmm5` (`blkInit`, `zl8`), and `ecx`
  counts the groups left.
* The layers with `len = 4` and `len = 2` (`layerFlat`) are loops over
  sixteen coefficients, the vectors at `[eax]` and `[eax + 16]`, which are
  gathered into the `a`s (`xmm1`) and the `b`s (`xmm0`) of eight
  butterflies (`gath4`, `gath2`), whose results are scattered back
  (`scat4`, `scat2`), with the two zetas of the step each in four words of
  `xmm5` (`zl4`), or its four zetas each in two words (`zl2`).

## `multiplyNTTs(h, f, g, scratch)` (Algorithm 11)

Products of two coefficients (less than `q² < 2³²`), and the sums of two of
them (less than `2q²`), are reduced with a Barrett reduction whose quotient
is the high half of a `mul` (`red`): `x - ⌊x · 1290167 / 2³²⌋ · q` is less
than `2q` and congruent to `x`, and one conditional subtraction (`csub`)
finishes it. The table of the `γᵢ` (`gammaTable`) is stored in `scratch`
first, as 128 `u32`s (`table`), and read through a pointer in `ebp`. For
each pair, with `ebx = h + 8i`, `esi = f + 8i`, `edi = g + 8i` and `ebp` at
`γᵢ`: `h[2i] = f[2i] g[2i] + (f[2i+1] g[2i+1] mod q) γᵢ` and
`h[2i+1] = f[2i] g[2i+1] + f[2i+1] g[2i]`, each reduced, accumulated in
`ecx`; the loop compares its pointer with the end of `h`, which is stored
in the argument slot of `scratch` once the table is written.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

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

/-- The 128 entries of `T` as `u32`s at `[b]`, through `edx`. -/
def table (T : List Nat) (b : Reg) : List Instr :=
  (List.range 128).flatMap fun k => [.mov .edx (.imm (BitVec.ofNat 32 (T.getD k 0))), .store (at_ b (4 * k)) .edx]

/-- `r ← (x mod q)` from `eax = r = x < 2³²`, with `edx` as a temporary:
`x - ⌊x · 1290167 / 2³²⌋ · q`, then `csub`. -/
def red (r : Reg) : List Instr :=
  [.mov .edx (.imm 1290167), .mul .edx, .mov .eax (.imm 3329), .mul .edx, .alu .sub r (.reg .eax)] +++
    csub r .edx

/-! ## `ntt` and `nttInv` -/

/-- `ζ^BitRev7(k) · 2¹⁶ mod q` for `k < 128`: the zetas in Montgomery form. -/
def montZetas : List Nat := zetaTable.map fun z => z * 65536 % 3329

/-- The table of `NTT⁻¹`: entry `k` is `ζ^BitRev7(128 - k) · 2¹⁶ mod q`, the
zetas in the order of use. -/
def montZetasRev : List Nat := (List.range 128).map fun k => montZetas.getD ((128 - k) % 128) 0

/-- The 128 entries of `T` as words at `[eax]`, two at a time through `edx`. -/
def wtable (T : List Nat) : List Instr :=
  (List.range 64).flatMap fun k =>
    [.mov .edx (.imm (BitVec.ofNat 32 (T.getD (2 * k) 0 + 65536 * T.getD (2 * k + 1) 0))),
      .store (at_ .eax (4 * k)) .edx]

/-! ## The butterflies -/

/-- The butterflies of Algorithm 9 on the `a`s in `xmm1` and the `b`s in
`xmm0`, with the zetas in `xmm5`: `a + ζ b` in `xmm3` and `a - ζ b` in `xmm1`. -/
def fCore : List Instr :=
  wmont .xmm0 .xmm5 .xmm2 +++ wcadd .xmm0 .xmm2 +++
  ([wmov .xmm3 .xmm1, wb .paddw .xmm3 .xmm0] : List Instr) +++ wcsub .xmm3 .xmm2 +++
  ([wb .psubw .xmm1 .xmm0] : List Instr) +++ wcadd .xmm1 .xmm2

/-- The butterflies of Algorithm 10: `a + b` in `xmm3` and `ζ (b - a)` in `xmm0`. -/
def iCore : List Instr :=
  ([wmov .xmm3 .xmm1, wb .paddw .xmm3 .xmm0] : List Instr) +++ wcsub .xmm3 .xmm2 +++
  ([wb .psubw .xmm0 .xmm1] : List Instr) +++ wmont .xmm0 .xmm5 .xmm2 +++ wcadd .xmm0 .xmm2

/-- Eight butterflies of a layer with `len ≥ 8` (`d = 2 · len`), on the
vectors at `[eax]` and `[eax + d]`; `rd` is the register `core` leaves the
second results in. -/
def lBody (core : List Instr) (rd : XReg) (d : Nat) : List Instr :=
  ([.movdquLoad .xmm0 (at_ .eax d), .movdquLoad .xmm1 (at_ .eax 0)] : List Instr) +++ core +++
  ([.movdquStore (at_ .eax 0) .xmm3, .movdquStore (at_ .eax d) rd] : List Instr)

/-- The butterflies of two blocks with `len = 4`: the `a`s (words 0 to 3 of
the vectors at `[eax]` and `[eax + 16]`) in `xmm1` and the `b`s in `xmm0`. -/
def gath4 : List Instr :=
  [.movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 16), wmov .xmm1 .xmm0, wb .punpckhqdq .xmm0 .xmm2,
    wb .punpcklqdq .xmm1 .xmm2]

/-- The butterflies of four blocks with `len = 2`: the `a`s (words 0, 1, 4
and 5 of each vector) in `xmm1` and the `b`s in `xmm0`. -/
def gath2 : List Instr :=
  [.movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 16), .xop (.pshufd .xmm0 .xmm0 0xD8),
    .xop (.pshufd .xmm2 .xmm2 0xD8), wmov .xmm1 .xmm0, wb .punpckhqdq .xmm0 .xmm2, wb .punpcklqdq .xmm1 .xmm2]

/-- The first results in `xmm3` and the second in `rd`, back to where
`gath4` took them from. -/
def scat4 (rd : XReg) : List Instr :=
  [wmov .xmm2 .xmm3, wb .punpcklqdq .xmm2 rd, wb .punpckhqdq .xmm3 rd, .movdquStore (at_ .eax 0) .xmm2,
    .movdquStore (at_ .eax 16) .xmm3]

/-- The same for `gath2`. -/
def scat2 (rd : XReg) : List Instr :=
  [wmov .xmm2 .xmm3, wb .punpckldq .xmm2 rd, wb .punpckhdq .xmm3 rd, .movdquStore (at_ .eax 0) .xmm2,
    .movdquStore (at_ .eax 16) .xmm3]

/-- Sixteen coefficients of the layer with `len = 4`. -/
def body4 (core : List Instr) (rd : XReg) : List Instr := gath4 +++ core +++ scat4 rd

/-- Sixteen coefficients of the layer with `len = 2`. -/
def body2 (core : List Instr) (rd : XReg) : List Instr := gath2 +++ core +++ scat2 rd

/-- The zeta at `[edx]` in every word of `xmm5`. -/
def zl8 : List Instr :=
  [.movqLoad .xmm5 (at_ .edx 0), wb .punpcklwd .xmm5 .xmm5, .xop (.pshufd .xmm5 .xmm5 0)]

/-- The two zetas at `[edx]`, each in four words of `xmm5`. -/
def zl4 : List Instr :=
  [.movqLoad .xmm5 (at_ .edx 0), wb .punpcklwd .xmm5 .xmm5, .xop (.pshufd .xmm5 .xmm5 0x50)]

/-- The four zetas at `[edx]`, each in two words of `xmm5`. -/
def zl2 : List Instr := [.movqLoad .xmm5 (at_ .edx 0), wb .punpcklwd .xmm5 .xmm5]

/-! ## The loops -/

/-- `eax ←` the words. -/
def layStart : List Instr := [.mov .eax (.mem (at_ .esp 24)), .alu .sub .eax (.imm 512)]

/-- The zeta of a block in every word of `xmm5`, `edx` on to the next one,
and the groups of eight butterflies of the block in `ecx`. -/
def blkInit (len : Nat) : List Instr :=
  zl8 +++ ([.alu .add .edx (.imm 2), .mov .ecx (.imm (BitVec.ofNat 32 (len / 8)))] : List Instr)

/-- The next group of eight butterflies. -/
def groupEnd : List Instr := [.alu .add .eax (.imm 16), .alu .sub .ecx (.imm 1)]

/-- The next block, if any. -/
def blkEnd (len : Nat) : List Instr :=
  [.alu .add .eax (.imm (BitVec.ofNat 32 (2 * len))), .alu .cmp .eax (.mem (at_ .esp 24))]

/-- A layer with `len ≥ 8`, eight butterflies at a time by `body (2 · len)`. -/
def layer8 (body : Nat → List Instr) (len : Nat) : Prog isa :=
  .seq (.block layStart)
    (.loop (.seq (.block (blkInit len))
      (.seq (.loop (.block (body (2 * len) +++ groupEnd)) .ne) (.block (blkEnd len)))) .ne)

/-- The next sixteen coefficients, `dz` bytes of zetas on. -/
def flatEnd (dz : Nat) : List Instr :=
  [.alu .add .eax (.imm 32), .alu .add .edx (.imm (BitVec.ofNat 32 dz)), .alu .cmp .eax (.mem (at_ .esp 24))]

/-- A layer with `len < 8`, sixteen coefficients at a time: the zetas by
`zl`, `dz` bytes of them. -/
def layerFlat (zl body : List Instr) (dz : Nat) : Prog isa :=
  .seq (.block layStart) (.loop (.block (zl +++ body +++ flatEnd dz)) .ne)

/-- `q` in the words of `xmm7` and `q⁻¹ mod 2¹⁶` in those of `xmm6`, and
`eax ← scratch`. -/
def nttConsts : List Instr :=
  wconst .xmm7 0x0D010D01 +++ wconst .xmm6 0xF301F301 +++ ([.mov .eax (.mem (at_ .esp 24))] : List Instr)

/-- The table `T` at `[eax]`, `edx` at its entry 1, and the end of the
words, `scratch + 1024`, in the slot of `scratch`. -/
def nttTable (T : List Nat) : List Instr :=
  wtable T +++
  ([.mov .edx (.reg .eax), .alu .add .edx (.imm 2), .alu .add .eax (.imm 1024), .store (at_ .esp 24) .eax] :
    List Instr)

/-- The constants, and the table `T` in `scratch`. -/
def nttInit (T : List Nat) : Prog isa := .seq (.block nttConsts) (.block (nttTable T))

/-- `ecx ← f` and `eax ←` the words, after `init`. -/
def passStart (init : List Instr) : List Instr :=
  init +++ ([.mov .ecx (.mem (at_ .esp 20)), .mov .eax (.mem (at_ .esp 24)), .alu .sub .eax (.imm 512)] : List Instr)

/-- Eight coefficients, `u32`s at `[ecx]`, to words at `[eax]`. -/
def wpackStep : List Instr :=
  [.movdquLoad .xmm0 (at_ .ecx 0), .movdquLoad .xmm1 (at_ .ecx 16), wb .packssdw .xmm0 .xmm1,
    .movdquStore (at_ .eax 0) .xmm0, .alu .add .ecx (.imm 32), .alu .add .eax (.imm 16),
    .alu .cmp .eax (.mem (at_ .esp 24))]

/-- The coefficients of `f` to the words. -/
def wpackPass : Prog isa := .seq (.block (passStart [])) (.loop (.block wpackStep) .ne)

/-- Eight coefficients, words at `[eax]`, through `core` on `xmm0`, to
`u32`s at `[ecx]` (`xmm4` is zero). -/
def wunpackStep (core : List Instr) : List Instr :=
  ([.movdquLoad .xmm0 (at_ .eax 0)] : List Instr) +++ core +++
  ([wmov .xmm1 .xmm0, wb .punpcklwd .xmm0 .xmm4, wb .punpckhwd .xmm1 .xmm4, .movdquStore (at_ .ecx 0) .xmm0,
    .movdquStore (at_ .ecx 16) .xmm1, .alu .add .ecx (.imm 32), .alu .add .eax (.imm 16),
    .alu .cmp .eax (.mem (at_ .esp 24))] : List Instr)

/-- The words, through `core`, to the coefficients of `f`, after `init`. -/
def wunpackPass (init core : List Instr) : Prog isa :=
  .seq (.block (passStart (wb .pxor .xmm4 .xmm4 :: init))) (.loop (.block (wunpackStep core)) .ne)

def ntt : Prog isa :=
  wframe (.seq (nttInit montZetas) (.seq wpackPass
    (.seq (layer8 (lBody fCore .xmm1) 128) (.seq (layer8 (lBody fCore .xmm1) 64)
      (.seq (layer8 (lBody fCore .xmm1) 32) (.seq (layer8 (lBody fCore .xmm1) 16)
        (.seq (layer8 (lBody fCore .xmm1) 8) (.seq (layerFlat zl4 (body4 fCore .xmm1) 4)
          (.seq (layerFlat zl2 (body2 fCore .xmm1) 8) (wunpackPass [] []))))))))))

/-- `3303 · 2¹⁶ mod q = 512` in the words of `xmm5`. -/
def scaleInit : List Instr := wconst .xmm5 0x02000200

/-- `xmm0 ← xmm0 · 3303 mod q` in each word. -/
def scaleCore : List Instr := wmont .xmm0 .xmm5 .xmm2 +++ wcadd .xmm0 .xmm2

def nttInv : Prog isa :=
  wframe (.seq (nttInit montZetasRev) (.seq wpackPass
    (.seq (layerFlat zl2 (body2 iCore .xmm0) 8) (.seq (layerFlat zl4 (body4 iCore .xmm0) 4)
      (.seq (layer8 (lBody iCore .xmm0) 8) (.seq (layer8 (lBody iCore .xmm0) 16)
        (.seq (layer8 (lBody iCore .xmm0) 32) (.seq (layer8 (lBody iCore .xmm0) 64)
          (.seq (layer8 (lBody iCore .xmm0) 128) (wunpackPass scaleInit scaleCore))))))))))

/-! ## `multiplyNTTs` -/

/-- The pair `i`: `h[2i]` and `h[2i + 1]`. -/
def mulBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 4)), .mov .edx (.mem (at_ .edi 4)), .mul .edx, .mov .ecx (.reg .eax)] +++
  red .ecx +++
  [.mov .eax (.reg .ecx), .mov .edx (.mem (at_ .ebp 0)), .mul .edx, .mov .ecx (.reg .eax),
    .mov .eax (.mem (at_ .esi 0)), .mov .edx (.mem (at_ .edi 0)), .mul .edx, .alu .add .ecx (.reg .eax),
    .mov .eax (.reg .ecx)] +++ red .ecx +++
  [.store (at_ .ebx 0) .ecx, .mov .eax (.mem (at_ .esi 0)), .mov .edx (.mem (at_ .edi 4)), .mul .edx,
    .mov .ecx (.reg .eax), .mov .eax (.mem (at_ .esi 4)), .mov .edx (.mem (at_ .edi 0)), .mul .edx,
    .alu .add .ecx (.reg .eax), .mov .eax (.reg .ecx)] +++ red .ecx +++
  [.store (at_ .ebx 4) .ecx, .alu .add .ebx (.imm 8), .alu .add .esi (.imm 8), .alu .add .edi (.imm 8),
    .alu .add .ebp (.imm 4), .alu .cmp .ebx (.mem (at_ .esp 32))]

/-- `eax = scratch`. -/
def mulLd : List Instr := [.mov .eax (.mem (at_ .esp 32))]

/-- The gamma table, `ebp = scratch`, `h + 1024` in the slot of `scratch`, and the pointers. -/
def mulSetup : List Instr :=
  table gammaTable .eax +++
  [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 20)), .mov .edx (.reg .ebx), .alu .add .edx (.imm 1024),
    .store (at_ .esp 32) .edx, .mov .esi (.mem (at_ .esp 24)), .mov .edi (.mem (at_ .esp 28))]

def multiplyNTTs : Prog isa :=
  leaf (.seq (.block mulLd) (.seq (.block mulSetup) (.loop (.block mulBody) .ne)))

end VG.Impl.MlKem.X86
