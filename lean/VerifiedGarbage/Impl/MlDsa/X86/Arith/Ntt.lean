module

public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

## `ntt(f, scratch)` (Algorithm 41)

Four butterflies at a time, on the doublewords of XMM registers, with the
pieces of `Impl/MlDsa/X86/Arith/Mul.lean` (`vmont`, `vmont2`), inside the
MCDT frame `pmuludq` needs; the function uses only `eax`, `ecx`, `edx` and
the XMM registers, and its arguments are at `[esp + 16]` and `[esp + 20]`
there. A table of 256 zetas in Montgomery form (times `2³² mod q`) is
stored in `scratch` as `u32`s (`table`, through `edx`), and read through
`edx`, which moves up it from entry 1, a block at a time; the end of the
polynomial, `f + 1024`, is stored in the argument slot of `scratch`, which
the loops compare `eax` with (`nttInit`).

The coefficients are not reduced between the layers: a butterfly
(`bfTail`) leaves `a + t` and `a + 2q - t` for `t`, the Montgomery product
of `b` and the zeta, less than `2q` (`vmont`), so after `l` layers they are
less than `(1 + 2l) · q`. The model has no `psubd`: `a + 2q - t` is
`a + (2q + 1) + (t xor 0xFFFFFFFF)`, with `2q + 1` in the doublewords of
`xmm3` and `0xFFFFFFFF` in those of `xmm4` (`q` is in those of `xmm7` and
`-q⁻¹ mod 2³²` in those of `xmm6`, for `vmont`).

* A layer with `len ≥ 4` (`layer4`) is a loop over its blocks, each a loop
  over its groups of four butterflies (`fBody`): `eax` points at
  coefficient `j`, `[eax + 4·len]` is coefficient `j + len`, the zeta of
  the block is in every doubleword of `xmm5` (`blkInit`), and `ecx` counts
  the groups left.
* The layers with `len = 2` and `len = 1` (`layerFlat`) are loops over
  eight coefficients, the vectors at `[eax]` and `[eax + 16]`, which are
  gathered into the `a`s (`xmm1`) and the `b`s (`xmm0`) of four butterflies
  (`gath2`, `gath1`), whose results are scattered back (`scat2`, `scat1`).
  With `len = 2` the two blocks' zetas are in doublewords 0 and 2 of `xmm5`
  (`zl2`), which `vmont` reads; with `len = 1` the four blocks' are its
  doublewords (`zl1`), and `vmont2` multiplies doubleword by doubleword.
  Both use `xmm5` as their temporary, so that `xmm1` keeps the `a`s.
* A last pass (`pass finInit finCore`) reduces every coefficient `x < 17q`:
  `x - (x >> 23) · q = (x mod 2²³) + (k << 13) - k` for `k = x >> 23` is
  less than `2q` (`finFold`, which also subtracts `q`), and `q` is added
  back where that is negative (`finSub`).

## `nttInv(f, scratch)` (Algorithm 42)

The same pieces, in the other order: the layers with `len = 1` and
`len = 2` (`layerFlat`), then those with `len` = 4, …, 128 (`layer4`). The
table (`montNegZetaRev`) holds the negated zetas (the `z` of Algorithm 42)
in the order of use, so that `edx` moves up it from entry 1 as in `ntt`. A
butterfly leaves `a + b` and the Montgomery product of `a + 128q - b` and
the zeta (`iBody`, `iBody2`, `iBody1`: `bfTail` on the `a`s and the `b`s,
with `128q + 1` in the doublewords of `xmm3`, then `vmont` or `vmont2`), so
the coefficients are less than `2^l · q` after `l` layers, and the sums and
`a + 128q` stay below `2³²`. A last pass (`pass scaleInit scaleCore`)
multiplies every coefficient by `8347681 = 256⁻¹ mod q`, in Montgomery
form, and reduces it (`vmont`, `vcsub`).

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.Arith

open VG.X86
open VG.Impl.MlKem.X86 (at_)

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `ζ^BitRev8(m) · 2³² mod q` for `m < 256`; the proofs check that it is
(`VG.Proof.MlDsa.X86.Arith.montZeta_eq`). -/
def montZetaTable : List Nat := [
  4193792, 25847, 5771523, 7861508, 237124, 7602457, 7504169, 466468, 1826347, 2353451, 8021166,
  6288512, 3119733, 5495562, 3111497, 2680103, 2725464, 1024112, 7300517, 3585928, 7830929,
  7260833, 2619752, 6271868, 6262231, 4520680, 6980856, 5102745, 1757237, 8360995, 4010497, 280005,
  2706023, 95776, 3077325, 3530437, 6718724, 4788269, 5842901, 3915439, 4519302, 5336701, 3574422,
  5512770, 3539968, 8079950, 2348700, 7841118, 6681150, 6736599, 3505694, 4558682, 3507263,
  6239768, 6779997, 3699596, 811944, 531354, 954230, 3881043, 3900724, 5823537, 2071892, 5582638,
  4450022, 6851714, 4702672, 5339162, 6927966, 3475950, 2176455, 6795196, 7122806, 1939314,
  4296819, 7380215, 5190273, 5223087, 4747489, 126922, 3412210, 7396998, 2147896, 2715295, 5412772,
  4686924, 7969390, 5903370, 7709315, 7151892, 8357436, 7072248, 7998430, 1349076, 1852771,
  6949987, 5037034, 264944, 508951, 3097992, 44288, 7280319, 904516, 3958618, 4656075, 8371839,
  1653064, 5130689, 2389356, 8169440, 759969, 7063561, 189548, 4827145, 3159746, 6529015, 5971092,
  8202977, 1315589, 1341330, 1285669, 6795489, 7567685, 6940675, 5361315, 4499357, 4751448,
  3839961, 2091667, 3407706, 2316500, 3817976, 5037939, 2244091, 5933984, 4817955, 266997, 2434439,
  7144689, 3513181, 4860065, 4621053, 7183191, 5187039, 900702, 1859098, 909542, 819034, 495491,
  6767243, 8337157, 7857917, 7725090, 5257975, 2031748, 3207046, 4823422, 7855319, 7611795,
  4784579, 342297, 286988, 5942594, 4108315, 3437287, 5038140, 1735879, 203044, 2842341, 2691481,
  5790267, 1265009, 4055324, 1247620, 2486353, 1595974, 4613401, 1250494, 2635921, 4832145,
  5386378, 1869119, 1903435, 7329447, 7047359, 1237275, 5062207, 6950192, 7929317, 1312455,
  3306115, 6417775, 7100756, 1917081, 5834105, 7005614, 1500165, 777191, 2235880, 3406031, 7838005,
  5548557, 6709241, 6533464, 5796124, 4656147, 594136, 4603424, 6366809, 2432395, 2454455, 8215696,
  1957272, 3369112, 185531, 7173032, 5196991, 162844, 1616392, 3014001, 810149, 1652634, 4686184,
  6581310, 5341501, 3523897, 3866901, 269760, 2213111, 7404533, 1717735, 472078, 7953734, 1723600,
  6577327, 1910376, 6712985, 7276084, 8119771, 4546524, 5441381, 6144432, 7959518, 6094090, 183443,
  7403526, 1612842, 4834730, 7826001, 3919660, 8332111, 7018208, 3937738, 1400424, 7534263, 1976782]

/-- `-ζ^BitRev8(m) · 2³² mod q` for `m < 256`; the proofs check that it is
(`VG.Proof.MlDsa.X86.Arith.montNegZeta_eq`). -/
def montNegZetaTable : List Nat := [
  4186625, 8354570, 2608894, 518909, 8143293, 777960, 876248, 7913949, 6554070, 6026966, 359251,
  2091905, 5260684, 2884855, 5268920, 5700314, 5654953, 7356305, 1079900, 4794489, 549488, 1119584,
  5760665, 2108549, 2118186, 3859737, 1399561, 3277672, 6623180, 19422, 4369920, 8100412, 5674394,
  8284641, 5303092, 4849980, 1661693, 3592148, 2537516, 4464978, 3861115, 3043716, 4805995,
  2867647, 4840449, 300467, 6031717, 539299, 1699267, 1643818, 4874723, 3821735, 4873154, 2140649,
  1600420, 4680821, 7568473, 7849063, 7426187, 4499374, 4479693, 2556880, 6308525, 2797779,
  3930395, 1528703, 3677745, 3041255, 1452451, 4904467, 6203962, 1585221, 1257611, 6441103,
  4083598, 1000202, 3190144, 3157330, 3632928, 8253495, 4968207, 983419, 6232521, 5665122, 2967645,
  3693493, 411027, 2477047, 671102, 1228525, 22981, 1308169, 381987, 7031341, 6527646, 1430430,
  3343383, 8115473, 7871466, 5282425, 8336129, 1100098, 7475901, 4421799, 3724342, 8578, 6727353,
  3249728, 5991061, 210977, 7620448, 1316856, 8190869, 3553272, 5220671, 1851402, 2409325, 177440,
  7064828, 7039087, 7094748, 1584928, 812732, 1439742, 3019102, 3881060, 3628969, 4540456, 6288750,
  4972711, 6063917, 4562441, 3342478, 6136326, 2446433, 3562462, 8113420, 5945978, 1235728,
  4867236, 3520352, 3759364, 1197226, 3193378, 7479715, 6521319, 7470875, 7561383, 7884926,
  1613174, 43260, 522500, 655327, 3122442, 6348669, 5173371, 3556995, 525098, 768622, 3595838,
  8038120, 8093429, 2437823, 4272102, 4943130, 3342277, 6644538, 8177373, 5538076, 5688936,
  2590150, 7115408, 4325093, 7132797, 5894064, 6784443, 3767016, 7129923, 5744496, 3548272,
  2994039, 6511298, 6476982, 1050970, 1333058, 7143142, 3318210, 1430225, 451100, 7067962, 5074302,
  1962642, 1279661, 6463336, 2546312, 1374803, 6880252, 7603226, 6144537, 4974386, 542412, 2831860,
  1671176, 1846953, 2584293, 3724270, 7786281, 3776993, 2013608, 5948022, 5925962, 164721, 6423145,
  5011305, 8194886, 1207385, 3183426, 8217573, 6764025, 5366416, 7570268, 6727783, 3694233,
  1799107, 3038916, 4856520, 4513516, 8110657, 6167306, 975884, 6662682, 7908339, 426683, 6656817,
  1803090, 6470041, 1667432, 1104333, 260646, 3833893, 2939036, 2235985, 420899, 2286327, 8196974,
  976891, 6767575, 3545687, 554416, 4460757, 48306, 1362209, 4442679, 6979993, 846154, 6403635]

/-- `8347681 · 2³² mod q`: `256⁻¹` in Montgomery form. -/
def scaleImm : BitVec 32 := 16382

/-- The table of `NTT⁻¹`: entry `k` is `-ζ^BitRev8(256 - k) · 2³² mod q`,
the negated zetas in the order of use. -/
def montNegZetaRev : List Nat := (List.range 256).map fun k => montNegZetaTable.getD ((256 - k) % 256) 0

/-- The 256 entries of `T` as `u32`s at `[eax]`, through `edx`. -/
def table (T : List Nat) : List Instr :=
  (List.range 256).flatMap fun k => [.mov .edx (.imm (BitVec.ofNat 32 (T.getD k 0))), .store (at_ .eax (4 * k)) .edx]

/-! ## `ntt` -/

/-- A butterfly's sum and difference: from the `a`s in `xmm1` and the `t`s
in `xmm0`, `a + t` in `xmm1` and `a + c - t` in `xmm2`, with `c + 1` in the
doublewords of `xmm3`. -/
def bfTail : List Instr :=
  [xmov .xmm2 .xmm0, xb .pxor .xmm2 .xmm4, xb .paddd .xmm2 .xmm3, xb .paddd .xmm2 .xmm1, xb .paddd .xmm1 .xmm0]

/-- Four butterflies of a layer with `len ≥ 4` (`d = 4 · len`), on the
vectors at `[eax]` and `[eax + d]`, with the zeta in `xmm5`. -/
def fBody (d : Nat) : List Instr :=
  ([.movdquLoad .xmm0 (at_ .eax d)] : List Instr) +++ vmont .xmm0 .xmm5 .xmm2 .xmm1 +++
  ([.movdquLoad .xmm1 (at_ .eax 0)] : List Instr) +++ bfTail +++
  ([.movdquStore (at_ .eax 0) .xmm1, .movdquStore (at_ .eax d) .xmm2] : List Instr)

/-- The butterflies of two blocks with `len = 2`: the `b`s (coefficients 2,
3, 6 and 7 of the eight at `[eax]`) in `xmm0` and the `a`s in `xmm1`. -/
def gath2 : List Instr :=
  [.movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 16), xmov .xmm1 .xmm0, xb .punpckhqdq .xmm0 .xmm2,
    xb .punpcklqdq .xmm1 .xmm2]

/-- The butterflies of four blocks with `len = 1`: the `b`s (coefficients
1, 3, 5 and 7) in `xmm0` and the `a`s in `xmm1`. -/
def gath1 : List Instr :=
  [.movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 16), .xop (.pshufd .xmm0 .xmm0 0xD8),
    .xop (.pshufd .xmm2 .xmm2 0xD8), xmov .xmm1 .xmm0, xb .punpckhqdq .xmm0 .xmm2, xb .punpcklqdq .xmm1 .xmm2]

/-- The sums in `xmm1` and the differences in `xmm2`, back to where
`gath2` took them from. -/
def scat2 : List Instr :=
  [xmov .xmm0 .xmm1, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2, .movdquStore (at_ .eax 0) .xmm0,
    .movdquStore (at_ .eax 16) .xmm1]

/-- The same for `gath1`. -/
def scat1 : List Instr :=
  [xmov .xmm0 .xmm1, xb .punpckldq .xmm0 .xmm2, xb .punpckhdq .xmm1 .xmm2, .movdquStore (at_ .eax 0) .xmm0,
    .movdquStore (at_ .eax 16) .xmm1]

/-- The zetas of two blocks, in doublewords 0 and 2 of `xmm5`. -/
def zl2 : List Instr := [.movqLoad .xmm5 (at_ .edx 0), .xop (.pshufd .xmm5 .xmm5 0x98)]

/-- The zetas of four blocks, in the doublewords of `xmm5`. -/
def zl1 : List Instr := [.movdquLoad .xmm5 (at_ .edx 0)]

/-- Eight coefficients of the layer with `len = 2`. -/
def fBody2 : List Instr := gath2 +++ vmont .xmm0 .xmm5 .xmm2 .xmm5 +++ bfTail +++ scat2

/-- Eight coefficients of the layer with `len = 1`. -/
def fBody1 : List Instr := gath1 +++ vmont2 .xmm0 .xmm5 .xmm2 +++ bfTail +++ scat1

/-- `eax ← f`. -/
def layStart : List Instr := [.mov .eax (.mem (at_ .esp 16))]

/-- The zeta of a block in every doubleword of `xmm5`, `edx` on to the next
one, and the groups of four butterflies of the block in `ecx`. -/
def blkInit (len : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .edx 0)), .xop (.movd .xmm5 .ecx), .xop (.pshufd .xmm5 .xmm5 0), .alu .add .edx (.imm 4),
    .mov .ecx (.imm (BitVec.ofNat 32 (len / 4)))]

/-- The next group of four butterflies. -/
def groupEnd : List Instr := [.alu .add .eax (.imm 16), .alu .sub .ecx (.imm 1)]

/-- The next block, if any. -/
def blkEnd (len : Nat) : List Instr :=
  [.alu .add .eax (.imm (BitVec.ofNat 32 (4 * len))), .alu .cmp .eax (.mem (at_ .esp 20))]

/-- A layer with `len ≥ 4`, four butterflies at a time by `body (4 · len)`. -/
def layer4 (body : Nat → List Instr) (len : Nat) : Prog isa :=
  .seq (.block layStart)
    (.loop (.seq (.block (blkInit len))
      (.seq (.loop (.block (body (4 * len) +++ groupEnd)) .ne) (.block (blkEnd len)))) .ne)

/-- The next eight coefficients, `dz` bytes of zetas on. -/
def flatEnd (dz : Nat) : List Instr :=
  [.alu .add .eax (.imm 32), .alu .add .edx (.imm (BitVec.ofNat 32 dz)), .alu .cmp .eax (.mem (at_ .esp 20))]

/-- A layer with `len < 4`, eight coefficients at a time: the zetas by
`zl`, `dz` bytes of them. -/
def layerFlat (zl body : List Instr) (dz : Nat) : Prog isa :=
  .seq (.block layStart) (.loop (.block (zl +++ body +++ flatEnd dz)) .ne)

/-- The constants of the layers (`c + 1` for `bfTail` in `xmm3`), and
`eax ← scratch`. -/
def nttConsts (c3 : BitVec 32) : List Instr :=
  vconst .xmm7 qImm +++ vconst .xmm6 qInvImm +++ vconst .xmm4 0xFFFFFFFF +++ vconst .xmm3 c3 +++
  ([.mov .eax (.mem (at_ .esp 20))] : List Instr)

/-- The table `T` at `[eax]`, `edx` at its entry 1, and `f + 1024` in the
slot of `scratch`. -/
def nttTable (T : List Nat) : List Instr :=
  table T +++
  ([.mov .edx (.reg .eax), .alu .add .edx (.imm 4), .mov .eax (.mem (at_ .esp 16)), .alu .add .eax (.imm 1024),
    .store (at_ .esp 20) .eax] : List Instr)

/-- The constants, and the table `T` in `scratch`. -/
def nttInit (T : List Nat) (c3 : BitVec 32) : Prog isa := .seq (.block (nttConsts c3)) (.block (nttTable T))

/-- A pass over the coefficients, four at a time by `core` on `xmm0`. -/
def passStep (core : List Instr) : List Instr :=
  ([.movdquLoad .xmm0 (at_ .eax 0)] : List Instr) +++ core +++
  ([.movdquStore (at_ .eax 0) .xmm0, .alu .add .eax (.imm 16), .alu .cmp .eax (.mem (at_ .esp 20))] : List Instr)

/-- A pass, after `init` sets its constants. -/
def pass (init core : List Instr) : Prog isa :=
  .seq (.block (init +++ layStart)) (.loop (.block (passStep core)) .ne)

/-- `2q + 1`. -/
def fwdC : BitVec 32 := 16760835

/-- The constants of the last pass of `ntt`: `2²³ - 1` in the doublewords
of `xmm5` and `2³² - q + 1` in those of `xmm3`. -/
def finInit : List Instr := vconst .xmm5 0x7FFFFF +++ vconst .xmm3 4286586880

/-- `xmm0 ← x - (x >> 23) · q - q` for the doublewords `x` of `xmm0`. -/
def finFold : List Instr :=
  [xmov .xmm1 .xmm0, .xop (.shift .psrld .xmm1 23), xb .pand .xmm0 .xmm5, xmov .xmm2 .xmm1,
    .xop (.shift .pslld .xmm2 13), xb .paddd .xmm0 .xmm2, xb .pxor .xmm1 .xmm4, xb .paddd .xmm0 .xmm1,
    xb .paddd .xmm0 .xmm3]

/-- `q` added back to the doublewords of `xmm0` that are negative. -/
def finSub : List Instr :=
  [xmov .xmm1 .xmm0, .xop (.shift .psrld .xmm1 31), xb .paddd .xmm1 .xmm4, xb .pandn .xmm1 .xmm7,
    xb .paddd .xmm0 .xmm1]

/-- `xmm0 ← xmm0 mod q` for doublewords less than `17q`. -/
def finCore : List Instr := finFold +++ finSub

def ntt : Prog isa :=
  .frame (.mcdtEnter .eax)
    (.seq (nttInit montZetaTable fwdC)
      (.seq (layer4 fBody 128) (.seq (layer4 fBody 64) (.seq (layer4 fBody 32) (.seq (layer4 fBody 16)
        (.seq (layer4 fBody 8) (.seq (layer4 fBody 4) (.seq (layerFlat zl2 fBody2 8)
          (.seq (layerFlat zl1 fBody1 16) (pass finInit finCore))))))))))
    .mcdtLeave

/-! ## `nttInv` -/

/-- `128q + 1`. -/
def invC : BitVec 32 := 1072693377

/-- Four butterflies of a layer with `len ≥ 4` (`d = 4 · len`). -/
def iBody (d : Nat) : List Instr :=
  ([.movdquLoad .xmm0 (at_ .eax d), .movdquLoad .xmm1 (at_ .eax 0)] : List Instr) +++ bfTail +++
  ([.movdquStore (at_ .eax 0) .xmm1, xmov .xmm0 .xmm2] : List Instr) +++ vmont .xmm0 .xmm5 .xmm2 .xmm1 +++
  ([.movdquStore (at_ .eax d) .xmm0] : List Instr)

/-- Eight coefficients of the layer with `len = 2`. -/
def iBody2 : List Instr :=
  gath2 +++ bfTail +++ ([xmov .xmm0 .xmm2] : List Instr) +++ vmont .xmm0 .xmm5 .xmm2 .xmm5 +++
  ([xmov .xmm2 .xmm0] : List Instr) +++ scat2

/-- Eight coefficients of the layer with `len = 1`. -/
def iBody1 : List Instr :=
  gath1 +++ bfTail +++ ([xmov .xmm0 .xmm2] : List Instr) +++ vmont2 .xmm0 .xmm5 .xmm2 +++
  ([xmov .xmm2 .xmm0] : List Instr) +++ scat1

/-- The constants of the last pass of `nttInv`: `256⁻¹` in Montgomery form
in the doublewords of `xmm5` and `2³² - q` in those of `xmm3`. -/
def scaleInit : List Instr := vconst .xmm5 scaleImm +++ vconst .xmm3 4286586879

/-- `xmm0 ← xmm0 · 256⁻¹ mod q` for doublewords less than `256q`. -/
def scaleCore : List Instr := vmont .xmm0 .xmm5 .xmm2 .xmm1 +++ vcsub .xmm0 .xmm1

def nttInv : Prog isa :=
  .frame (.mcdtEnter .eax)
    (.seq (nttInit montNegZetaRev invC)
      (.seq (layerFlat zl1 iBody1 16) (.seq (layerFlat zl2 iBody2 8) (.seq (layer4 iBody 4) (.seq (layer4 iBody 8)
        (.seq (layer4 iBody 16) (.seq (layer4 iBody 32) (.seq (layer4 iBody 64) (.seq (layer4 iBody 128)
          (pass scaleInit scaleCore))))))))))
    .mcdtLeave

end VG.Impl.MlDsa.X86.Arith
