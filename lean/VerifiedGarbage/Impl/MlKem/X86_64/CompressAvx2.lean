module

public import VerifiedGarbage.Impl.MlKem.X86_64.Compress
public import VerifiedGarbage.Impl.MlKem.X86_64.Decode12Avx2

/-!
# ML-KEM on x86-64: `vg_mlkem_compress_encode_avx2` and `vg_mlkem_decode_decompress_avx2`

`vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress` (`Compress.lean`)
on eight coefficients at a time, in the doublewords of AVX2 registers, for
the widths 10 and 4; the width 1 (the message, once per operation) runs the
scalar loop of `Compress.lean`. There are no multiplications: the products
by the constants are sums of shifts.

* Compression (`f = rdi`, `d = esi`, `out = rdx` moved to `r8`, `rcx`
  counting down): each coefficient `x < q` is `((x · M_d + 262080) >> 19)
  mod 2ᵈ` as in the scalar code, with `x · M_d` the sum of its shifts (`M₁₀
  = 161271 = 2¹⁷ + 2¹⁵ - 2¹¹ - 2⁹ - 2³ - 1`, `M₄ = 2520 = 2¹¹ + 2⁹ - 2⁵ -
  2³`). The eight values are then packed: `vpsllvd` shifts the odd ones left
  by `d`, adding each quadword's high doubleword to its low one gives the
  `2d`-bit pair (masked for `d = 10`), and for `d = 10`, `vpsllvq` and
  `vpsrldq` add each lane's two pairs into a 40-bit value. `vpshufb` and
  `vextracti128` gather the `d` bytes of the eight in the low bytes of
  `xmm1`, the others zero.
  - `d = 10`: a group of eight is ten bytes, stored as 16 (the next group
    overwrites the last six); the last group (`r8 = out + 310`) is stored
    to `out + 304`, its bytes shifted up by six over the last six bytes of
    the group before it (`vpsrldq` of `xmm1` by 4), so that the code writes
    only the 320 bytes of `out`.
  - `d = 4`: four groups of eight are four bytes each, interleaved
    (`vpunpckldq`, `vpunpcklqdq`) into the 16 bytes of 32 coefficients.
* Decompression (`b = rdi`, `len = rsi`, `d = edx`, `f = rcx` moved to
  `rsi`, `rcx` counting down): `vbroadcasti128` loads 16 bytes into both
  lanes, `vpshufb` puts the two bytes that hold value `j` in the low half of
  doubleword `j`, `vpsrlvd` and `vpand` extract it, and each value `y` is
  decompressed to `(q · y + 2ᵈ⁻¹) >> d`, with `q · y = y + 2⁸ y - 2¹⁰ y +
  2¹² y`.
  - `d = 10`: a group of eight is ten bytes; the last group is loaded from
    six bytes before it, with a mask that takes bytes 6 to 15 (`ymm12`), so
    that the code reads only the 320 bytes of `b`.
  - `d = 4`: one load holds 32 values, extracted with four masks.

The constants are built in registers, through `rax`, `ymm0` and `ymm1`
(`yconst4`, `yconst`). Both clear the upper halves of the vector registers
before returning (`vzeroupper`). Every address and branch depends only on
the pointers and `d`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `ymm d ← ymm a << n` and `>> n` (each doubleword). -/
def ysl (d a : XReg) (n : Nat) : Instr := .vop (.vshift .pslld .l256 d a (BitVec.ofNat 8 n))
def ysr (d a : XReg) (n : Nat) : Instr := .vop (.vshift .psrld .l256 d a (BitVec.ofNat 8 n))

/-! ## Compression -/

/-- `ymm1 ← x · 161271` for the doublewords `x` of `ymm0`, through `ymm2` and `ymm3`. -/
def ceMul10 : List Instr :=
  [ysl .xmm1 .xmm0 17, ysl .xmm2 .xmm0 15, yb .vpaddd .xmm1 .xmm1 .xmm2,
    ysl .xmm2 .xmm0 11, ysl .xmm3 .xmm0 9, yb .vpaddd .xmm2 .xmm2 .xmm3, yb .vpsubd .xmm1 .xmm1 .xmm2,
    ysl .xmm2 .xmm0 3, yb .vpaddd .xmm2 .xmm2 .xmm0, yb .vpsubd .xmm1 .xmm1 .xmm2]

/-- `ymm1 ← x · 2520` for the doublewords `x` of `ymm0`, through `ymm2` and `ymm3`. -/
def ceMul4 : List Instr :=
  [ysl .xmm1 .xmm0 11, ysl .xmm2 .xmm0 9, yb .vpaddd .xmm1 .xmm1 .xmm2,
    ysl .xmm2 .xmm0 5, ysl .xmm3 .xmm0 3, yb .vpaddd .xmm2 .xmm2 .xmm3, yb .vpsubd .xmm1 .xmm1 .xmm2]

/-- `ymm1 ← ((ymm1 + 262080) >> 19) ∧ (2ᵈ - 1)`, with `262080` in `ymm12` and `2ᵈ - 1` in `ymm13`. -/
def ceRound : List Instr := [yb .vpaddd .xmm1 .xmm1 .xmm12, ysr .xmm1 .xmm1 19, yb .vpand .xmm1 .xmm1 .xmm13]

/-- The `d` bytes of the eight `d`-bit values in `ymm1`, in the low bytes of
`xmm1` (the others zero), through `ymm2`: `ymm8` holds the shifts `0, d` of
`vpsllvd`, `ymm11` the mask of `vpshufb`; for `d = 10` (`wide`), `ymm9` the
mask `2²⁰ - 1` of each quadword and `ymm10` the shifts `0, 20` of `vpsllvq`. -/
def cePack (wide : Bool) : List Instr :=
  [.vop (.vvar .vpsllvd .l256 .xmm1 .xmm1 .xmm8), .vop (.vshift .psrlq .l256 .xmm2 .xmm1 32),
    yb .vpaddd .xmm1 .xmm1 .xmm2] ++
  (if wide then
    [yb .vpand .xmm1 .xmm1 .xmm9, .vop (.vvar .vpsllvq .l256 .xmm1 .xmm1 .xmm10),
      .vop (.vshift .psrldq .l256 .xmm2 .xmm1 8), yb .vpaddq .xmm1 .xmm1 .xmm2]
  else []) ++
  [yb .vpshufb .xmm1 .xmm1 .xmm11, .vop (.vextracti128 .xmm2 .xmm1 1), .vop (.vbin .vpor .l128 .xmm1 .xmm1 .xmm2)]

/-- The eight coefficients at `rdi + o`, compressed to 10 bits and packed into `xmm1`. -/
def ce10Grp (o : Nat) : List Instr :=
  .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: ceMul10 ++ ceRound ++ cePack true

/-- The eight coefficients at `rdi + o`, compressed to 4 bits and packed into `xmm1`. -/
def ce4Grp (o : Nat) : List Instr :=
  .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: ceMul4 ++ ceRound ++ cePack false

/-- The constants of `d = 10`. -/
def ce10Consts : List Instr :=
  yconst4 .xmm8 0x0000000a00000000 0x0000000a00000000 0x0000000a00000000 0x0000000a00000000 ++
  yconst4 .xmm9 0xfffff 0xfffff 0xfffff 0xfffff ++ yconst4 .xmm10 0 20 0 20 ++
  yconst4 .xmm11 0x8080800403020100 0x8080808080808080 0x0201008080808080 0x8080808080800403 ++
  yconst .xmm12 262080 ++ yconst .xmm13 1023

/-- The constants of `d = 4`. -/
def ce4Consts : List Instr :=
  yconst4 .xmm8 0x0000000400000000 0x0000000400000000 0x0000000400000000 0x0000000400000000 ++
  yconst4 .xmm11 0x8080808080800800 0x8080808080808080 0x8080808008008080 0x8080808080808080 ++
  yconst .xmm12 262080 ++ yconst .xmm13 15

/-- `d = 10`: 31 groups of eight, then the last (see the module's documentation). -/
def ce10V : Prog isa :=
  .seq (.block (ce10Consts ++ [.mov32 .rcx (.imm 31)]))
    (.seq (.loop (.block (ce10Grp 0 ++
        [.vmovdquStore .l128 (at_ .r8 0) .xmm1, .alu .add .rdi (.imm 32), .alu .add .r8 (.imm 10),
          .alu .sub .rcx (.imm 1)])) .ne)
      (.block (.vop (.vshift .psrldq .l128 .xmm4 .xmm1 4) :: ce10Grp 0 ++
        [.vop (.vshift .pslldq .l128 .xmm1 .xmm1 6), .vop (.vbin .vpor .l128 .xmm1 .xmm1 .xmm4),
          .alu .sub .r8 (.imm 6), .vmovdquStore .l128 (at_ .r8 0) .xmm1, .vop .vzeroupper])))

/-- `d = 4`: eight groups of 32. -/
def ce4V : Prog isa :=
  .seq (.block (ce4Consts ++ [.mov32 .rcx (.imm 8)]))
    (.seq (.loop (.block (ce4Grp 0 ++ [.vop (.vmovdqa .l128 .xmm4 .xmm1)] ++ ce4Grp 32 ++
        [.vop (.vmovdqa .l128 .xmm5 .xmm1)] ++ ce4Grp 64 ++ [.vop (.vmovdqa .l128 .xmm6 .xmm1)] ++ ce4Grp 96 ++
        [.vop (.vbin .vpunpckldq .l128 .xmm4 .xmm4 .xmm5), .vop (.vbin .vpunpckldq .l128 .xmm6 .xmm6 .xmm1),
          .vop (.vbin .vpunpcklqdq .l128 .xmm4 .xmm4 .xmm6), .vmovdquStore .l128 (at_ .r8 0) .xmm4,
          .alu .add .rdi (.imm 128), .alu .add .r8 (.imm 16), .alu .sub .rcx (.imm 1)])) .ne)
      (.block [.vop .vzeroupper]))

def compressEncodeAvx2 : Prog isa :=
  .seq (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 1)])
    (.ite .e (ceLoop 1 8 1) (.seq (.block [.alu32 .cmp .rsi (.imm 4)]) (.ite .e ce4V ce10V)))

/-! ## Decompression -/

/-- `ymm o ← (q · y + r) >> d` for the doublewords `y` of `ymm x`, with `r` in
`ymm rr`, through `ymm t₁`, `ymm t₂`. -/
def ddMul (o x t₁ t₂ rr : XReg) (d : Nat) : List Instr :=
  [ysl o x 8, yb .vpaddd o o x, ysl t₁ x 12, ysl t₂ x 10, yb .vpsubd t₁ t₁ t₂, yb .vpaddd o o t₁,
    yb .vpaddd o o rr, ysr o o d]

/-- The eight values of the 10 bytes that the mask `m` selects from the 16 at
`rdi`, decompressed, to `rsi`. -/
def dd10Grp (m : XReg) : List Instr :=
  [.vbroadcasti128 .xmm0 (at_ .rdi 0), yb .vpshufb .xmm0 .xmm0 m, .vop (.vvar .vpsrlvd .l256 .xmm0 .xmm0 .xmm9),
    yb .vpand .xmm0 .xmm0 .xmm10] ++ ddMul .xmm1 .xmm0 .xmm2 .xmm3 .xmm11 10 ++
  [.vmovdquStore .l256 (at_ .rsi 0) .xmm1]

/-- The constants of `d = 10`: the masks (`ymm8`, and `ymm12` for the last
group), the shifts (`ymm9`), `2¹⁰ - 1` (`ymm10`) and `2⁹` (`ymm11`). -/
def dd10Consts : List Instr :=
  yconst4 .xmm8 0x8080020180800100 0x8080040380800302 0x8080070680800605 0x8080090880800807 ++
  yconst4 .xmm12 0x8080080780800706 0x80800a0980800908 0x80800d0c80800c0b 0x80800f0e80800e0d ++
  yconst4 .xmm9 0x0000000200000000 0x0000000600000004 0x0000000200000000 0x0000000600000004 ++
  yconst .xmm10 1023 ++ yconst .xmm11 512

def dd10V : Prog isa :=
  .seq (.block (dd10Consts ++ [.mov32 .rcx (.imm 31)]))
    (.seq (.loop (.block (dd10Grp .xmm8 ++ [.alu .add .rdi (.imm 10), .alu .add .rsi (.imm 32),
        .alu .sub .rcx (.imm 1)])) .ne)
      (.block (.alu .sub .rdi (.imm 6) :: dd10Grp .xmm12 ++ [.vop .vzeroupper])))

/-- The eight values of bytes `4k` to `4k + 3` of `ymm0` (mask `ymm (8 + k)`),
decompressed from 4 bits, to `rsi + 32 k`. -/
def dd4Grp (m : XReg) (k : Nat) : List Instr :=
  [yb .vpshufb .xmm1 .xmm0 m, .vop (.vvar .vpsrlvd .l256 .xmm1 .xmm1 .xmm12), yb .vpand .xmm1 .xmm1 .xmm13] ++
    ddMul .xmm2 .xmm1 .xmm3 .xmm4 .xmm14 4 ++ [.vmovdquStore .l256 (at_ .rsi (32 * k)) .xmm2]

/-- The constants of `d = 4`: the masks of the four groups of a load
(`ymm8` to `ymm11`), the shifts `0, 4` (`ymm12`), `15` (`ymm13`) and `8` (`ymm14`). -/
def dd4Consts : List Instr :=
  yconst4 .xmm8 0x8080800080808000 0x8080800180808001 0x8080800280808002 0x8080800380808003 ++
  yconst4 .xmm9 0x8080800480808004 0x8080800580808005 0x8080800680808006 0x8080800780808007 ++
  yconst4 .xmm10 0x8080800880808008 0x8080800980808009 0x8080800a8080800a 0x8080800b8080800b ++
  yconst4 .xmm11 0x8080800c8080800c 0x8080800d8080800d 0x8080800e8080800e 0x8080800f8080800f ++
  yconst4 .xmm12 0x0000000400000000 0x0000000400000000 0x0000000400000000 0x0000000400000000 ++
  yconst .xmm13 15 ++ yconst .xmm14 8

def dd4V : Prog isa :=
  .seq (.block (dd4Consts ++ [.mov32 .rcx (.imm 8)]))
    (.seq (.loop (.block (.vbroadcasti128 .xmm0 (at_ .rdi 0) :: dd4Grp .xmm8 0 ++ dd4Grp .xmm9 1 ++
        dd4Grp .xmm10 2 ++ dd4Grp .xmm11 3 ++
        [.alu .add .rdi (.imm 16), .alu .add .rsi (.imm 128), .alu .sub .rcx (.imm 1)])) .ne)
      (.block [.vop .vzeroupper]))

def decodeDecompressAvx2 : Prog isa :=
  .seq (.block [.mov32 .rdx (.reg .rdx), .mov .rsi (.reg .rcx), .alu32 .cmp .rdx (.imm 1)])
    (.ite .e (ddLoop 1 8 1) (.seq (.block [.alu32 .cmp .rdx (.imm 4)]) (.ite .e dd4V dd10V)))

end VG.Impl.MlKem.X86_64
