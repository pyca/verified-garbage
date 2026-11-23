module

public import VerifiedGarbage.Impl.MlKem.X86.Vec
public import VerifiedGarbage.Impl.MlKem.X86.Ntt

@[expose] public section

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

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
def packStep : List Instr :=
  [.movdquLoad .xmm0 (at_ .ecx 0), .movdquLoad .xmm1 (at_ .ecx 16), wb .packssdw .xmm0 .xmm1,
    .movdquStore (at_ .eax 0) .xmm0, .alu .add .ecx (.imm 32), .alu .add .eax (.imm 16),
    .alu .cmp .eax (.mem (at_ .esp 24))]

/-- The coefficients of `f` to the words. -/
def packPass : Prog isa := .seq (.block (passStart [])) (.loop (.block packStep) .ne)

/-- Eight coefficients, words at `[eax]`, through `core` on `xmm0`, to
`u32`s at `[ecx]` (`xmm4` is zero). -/
def unpackStep (core : List Instr) : List Instr :=
  ([.movdquLoad .xmm0 (at_ .eax 0)] : List Instr) +++ core +++
  ([wmov .xmm1 .xmm0, wb .punpcklwd .xmm0 .xmm4, wb .punpckhwd .xmm1 .xmm4, .movdquStore (at_ .ecx 0) .xmm0,
    .movdquStore (at_ .ecx 16) .xmm1, .alu .add .ecx (.imm 32), .alu .add .eax (.imm 16),
    .alu .cmp .eax (.mem (at_ .esp 24))] : List Instr)

/-- The words, through `core`, to the coefficients of `f`, after `init`. -/
def unpackPass (init core : List Instr) : Prog isa :=
  .seq (.block (passStart (wb .pxor .xmm4 .xmm4 :: init))) (.loop (.block (unpackStep core)) .ne)

def vntt : Prog isa :=
  wframe (.seq (nttInit montZetas) (.seq packPass
    (.seq (layer8 (lBody fCore .xmm1) 128) (.seq (layer8 (lBody fCore .xmm1) 64)
      (.seq (layer8 (lBody fCore .xmm1) 32) (.seq (layer8 (lBody fCore .xmm1) 16)
        (.seq (layer8 (lBody fCore .xmm1) 8) (.seq (layerFlat zl4 (body4 fCore .xmm1) 4)
          (.seq (layerFlat zl2 (body2 fCore .xmm1) 8) (unpackPass [] []))))))))))

/-- `3303 · 2¹⁶ mod q = 512` in the words of `xmm5`. -/
def scaleInit : List Instr := wconst .xmm5 0x02000200

/-- `xmm0 ← xmm0 · 3303 mod q` in each word. -/
def scaleCore : List Instr := wmont .xmm0 .xmm5 .xmm2 +++ wcadd .xmm0 .xmm2

def vnttInv : Prog isa :=
  wframe (.seq (nttInit montZetasRev) (.seq packPass
    (.seq (layerFlat zl2 (body2 iCore .xmm0) 8) (.seq (layerFlat zl4 (body4 iCore .xmm0) 4)
      (.seq (layer8 (lBody iCore .xmm0) 8) (.seq (layer8 (lBody iCore .xmm0) 16)
        (.seq (layer8 (lBody iCore .xmm0) 32) (.seq (layer8 (lBody iCore .xmm0) 64)
          (.seq (layer8 (lBody iCore .xmm0) 128) (unpackPass scaleInit scaleCore))))))))))

end VG.Impl.MlKem.X86
