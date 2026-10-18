module

public import VerifiedGarbage.Impl.MlKem.X86_64.CompressAvx2

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_compress_encode_avx2` and `vg_mlkem1024_decode_decompress_avx2`

`vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`
(`Compress.lean`) on eight coefficients at a time, in the doublewords of
AVX2 registers, as ML-KEM-768's (`Impl/MlKem/X86_64/CompressAvx2.lean`) for
its widths, 11 and 5. There are no multiplications: the products by the
constants are sums of shifts.

* Compression (`f = rdi`, `d = esi`, `out = rdx` moved to `r8`, `rcx`
  counting down): each coefficient `x < q` is `((x · M_d + 261888) >> 19)
  mod 2ᵈ` as in the scalar code, with `x · M_d` the sum of its shifts (`M₁₁ =
  322542 = 2¹⁸ + 2¹⁶ - 2¹² - 2¹⁰ - 2⁴ - 2`, `M₅ = 5040 = 2¹² + 2¹⁰ - 2⁶ -
  2⁴`). The eight values of a group are packed as ML-KEM-768's (`cePack
  true`): `vpsllvd` shifts the odd ones left by `d`, adding each quadword's
  high doubleword to its low one gives the `2d`-bit pair (masked), and
  `vpsllvq` and `vpsrldq` add each lane's two pairs into its `4d`-bit value,
  shifted left by 4 more bits in the high lane, so that the high lane's
  value starts at bit `4d` once its bytes follow the low lane's last but
  one: `vpshufb` places the low lane's `⌈d/2⌉` bytes from byte 0, and the
  high lane's from byte `⌊d/2⌋`, and `vextracti128` and `vpor` merge them
  (the byte they share holds the low lane's last 4 bits and the high lane's
  first 4) in the low `d` bytes of `xmm1`, the others zero.
  - `d = 11`: a group is 11 bytes, stored as 16 (the next group overwrites
    the last five); the last group (`r8 = out + 341`) is stored to
    `out + 336`, its bytes shifted up by five over the last five bytes of
    the group before it (`vpsrldq` of `xmm1` by 6), so that the code writes
    only the 352 bytes of `out`.
  - `d = 5`: two groups (10 bytes, the second's shifted up by five with
    `vpslldq`) are stored as 16, the next two overwriting the last six; the
    last two (`r8 = out + 150`) are stored to `out + 144`, shifted up by six
    over the last six bytes of the two before them (`vpsrldq` by 4), so that
    the code writes only the 160 bytes of `out`.
* Decompression (`b = rdi`, `len = rsi`, `d = edx`, `f = rcx` moved to
  `rsi`, `rcx` counting down): `vbroadcasti128` loads 16 bytes into both
  lanes, `vpshufb` puts the bytes that hold value `j` (two or three) in the
  low bytes of doubleword `j`, `vpsrlvd` and `vpand` extract it, and each
  value `y` is decompressed to `(q · y + 2ᵈ⁻¹) >> d`, with `q · y = y + 2⁸ y
  - 2¹⁰ y + 2¹² y`.
  - `d = 11`: a group of eight is 11 bytes; the last group is loaded from
    five bytes before it, with masks that take its bytes from byte 5
    (`ymm12`), so that the code reads only the 352 bytes of `b`.
  - `d = 5`: a load holds two groups of 5 bytes (masks `ymm8`, `ymm9`); the
    last two are loaded from six bytes before them (masks `ymm10`, `ymm11`),
    so that the code reads only the 160 bytes of `b`.

The constants are built in registers, through `rax`, `ymm0` and `ymm1`
(`yconst4`, `yconst`). Both clear the upper halves of the vector registers
before returning (`vzeroupper`). Every address and branch depends only on
the pointers and `d`.
-/

@[expose] public section

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

/-! ## Compression -/

/-- `ymm1 ← x · 322542` for the doublewords `x` of `ymm0`, through `ymm2` and `ymm3`. -/
def ceMul11 : List Instr :=
  [ysl .xmm1 .xmm0 18, ysl .xmm2 .xmm0 16, yb .vpaddd .xmm1 .xmm1 .xmm2,
    ysl .xmm2 .xmm0 12, ysl .xmm3 .xmm0 10, yb .vpaddd .xmm2 .xmm2 .xmm3, yb .vpsubd .xmm1 .xmm1 .xmm2,
    ysl .xmm2 .xmm0 4, ysl .xmm3 .xmm0 1, yb .vpaddd .xmm2 .xmm2 .xmm3, yb .vpsubd .xmm1 .xmm1 .xmm2]

/-- `ymm1 ← x · 5040` for the doublewords `x` of `ymm0`, through `ymm2` and `ymm3`. -/
def ceMul5 : List Instr :=
  [ysl .xmm1 .xmm0 12, ysl .xmm2 .xmm0 10, yb .vpaddd .xmm1 .xmm1 .xmm2,
    ysl .xmm2 .xmm0 6, ysl .xmm3 .xmm0 4, yb .vpaddd .xmm2 .xmm2 .xmm3, yb .vpsubd .xmm1 .xmm1 .xmm2]

/-- The eight coefficients at `rdi + o`, compressed to 11 bits and packed into `xmm1`. -/
def ce11Grp (o : Nat) : List Instr :=
  .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: ceMul11 ++ ceRound ++ cePack true

/-- The eight coefficients at `rdi + o`, compressed to 5 bits and packed into `xmm1`. -/
def ce5Grp (o : Nat) : List Instr :=
  .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: ceMul5 ++ ceRound ++ cePack true

/-- The constants of `d = 11`: the shifts `0, 11` of `vpsllvd` (`ymm8`), the
mask `2²² - 1` of each quadword (`ymm9`), the shifts `0, 22` and `4, 26` of
`vpsllvq` (`ymm10`), the masks of `vpshufb` (`ymm11`), `261888` (`ymm12`)
and `2¹¹ - 1` (`ymm13`). -/
def ce11Consts : List Instr :=
  yconst4 .xmm8 0x0000000b00000000 0x0000000b00000000 0x0000000b00000000 0x0000000b00000000 ++
  yconst4 .xmm9 0x3fffff 0x3fffff 0x3fffff 0x3fffff ++ yconst4 .xmm10 0 22 4 26 ++
  yconst4 .xmm11 0x8080050403020100 0x8080808080808080 0x0201008080808080 0x8080808080050403 ++
  yconst .xmm12 261888 ++ yconst .xmm13 2047

/-- The constants of `d = 5`: as those of `d = 11`, for the width 5. -/
def ce5Consts : List Instr :=
  yconst4 .xmm8 0x0000000500000000 0x0000000500000000 0x0000000500000000 0x0000000500000000 ++
  yconst4 .xmm9 0x3ff 0x3ff 0x3ff 0x3ff ++ yconst4 .xmm10 0 10 4 14 ++
  yconst4 .xmm11 0x8080808080020100 0x8080808080808080 0x8080800201008080 0x8080808080808080 ++
  yconst .xmm12 261888 ++ yconst .xmm13 31

/-- `d = 11`: 31 groups of eight, then the last (see the module's documentation). -/
def ce11V : Prog isa :=
  .seq (.block (ce11Consts ++ [.mov32 .rcx (.imm 31)]))
    (.seq (.loop (.block (ce11Grp 0 ++
        [.vmovdquStore .l128 (at_ .r8 0) .xmm1, .alu .add .rdi (.imm 32), .alu .add .r8 (.imm 11),
          .alu .sub .rcx (.imm 1)])) .ne)
      (.block (.vop (.vshift .psrldq .l128 .xmm4 .xmm1 6) :: ce11Grp 0 ++
        [.vop (.vshift .pslldq .l128 .xmm1 .xmm1 5), .vop (.vbin .vpor .l128 .xmm1 .xmm1 .xmm4),
          .alu .sub .r8 (.imm 5), .vmovdquStore .l128 (at_ .r8 0) .xmm1, .vop .vzeroupper])))

/-- Two groups of `d = 5`, from `rdi`, their 10 bytes packed into `xmm1` (through `xmm4`). -/
def ce5Pair : List Instr :=
  ce5Grp 0 ++ [.vop (.vmovdqa .l128 .xmm4 .xmm1)] ++ ce5Grp 32 ++
    [.vop (.vshift .pslldq .l128 .xmm1 .xmm1 5), .vop (.vbin .vpor .l128 .xmm1 .xmm1 .xmm4)]

/-- `d = 5`: 15 pairs of groups, then the last (see the module's documentation). -/
def ce5V : Prog isa :=
  .seq (.block (ce5Consts ++ [.mov32 .rcx (.imm 15)]))
    (.seq (.loop (.block (ce5Pair ++
        [.vmovdquStore .l128 (at_ .r8 0) .xmm1, .alu .add .rdi (.imm 64), .alu .add .r8 (.imm 10),
          .alu .sub .rcx (.imm 1)])) .ne)
      (.block (.vop (.vshift .psrldq .l128 .xmm5 .xmm1 4) :: ce5Pair ++
        [.vop (.vshift .pslldq .l128 .xmm1 .xmm1 6), .vop (.vbin .vpor .l128 .xmm1 .xmm1 .xmm5),
          .alu .sub .r8 (.imm 6), .vmovdquStore .l128 (at_ .r8 0) .xmm1, .vop .vzeroupper])))

def compressEncode1024Avx2 : Prog isa :=
  .seq (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 5)])
    (.ite .e ce5V ce11V)

/-! ## Decompression -/

/-- The eight values of the 11 bytes that the mask `m` selects from the 16 at
`rdi`, decompressed, to `rsi`. -/
def dd11Grp (m : XReg) : List Instr :=
  [.vbroadcasti128 .xmm0 (at_ .rdi 0), yb .vpshufb .xmm0 .xmm0 m, .vop (.vvar .vpsrlvd .l256 .xmm0 .xmm0 .xmm9),
    yb .vpand .xmm0 .xmm0 .xmm10] ++ ddMul .xmm1 .xmm0 .xmm2 .xmm3 .xmm11 11 ++
  [.vmovdquStore .l256 (at_ .rsi 0) .xmm1]

/-- The constants of `d = 11`: the masks (`ymm8`, and `ymm12` for the last
group), the shifts (`ymm9`), `2¹¹ - 1` (`ymm10`) and `2¹⁰` (`ymm11`). -/
def dd11Consts : List Instr :=
  yconst4 .xmm8 0x8080020180800100 0x8080050480040302 0x8008070680800605 0x80800a0980800908 ++
  yconst4 .xmm12 0x8080070680800605 0x80800a0980090807 0x800d0c0b80800b0a 0x80800f0e80800e0d ++
  yconst4 .xmm9 0x0000000300000000 0x0000000100000006 0x0000000700000004 0x0000000500000002 ++
  yconst .xmm10 2047 ++ yconst .xmm11 1024

def dd11V : Prog isa :=
  .seq (.block (dd11Consts ++ [.mov32 .rcx (.imm 31)]))
    (.seq (.loop (.block (dd11Grp .xmm8 ++ [.alu .add .rdi (.imm 11), .alu .add .rsi (.imm 32),
        .alu .sub .rcx (.imm 1)])) .ne)
      (.block (.alu .sub .rdi (.imm 5) :: dd11Grp .xmm12 ++ [.vop .vzeroupper])))

/-- The eight values of the bytes of `ymm0` that the masks `ymm m` select,
decompressed from 5 bits, to `rsi + 32 k`. -/
def dd5Grp (m : XReg) (k : Nat) : List Instr :=
  [yb .vpshufb .xmm1 .xmm0 m, .vop (.vvar .vpsrlvd .l256 .xmm1 .xmm1 .xmm12), yb .vpand .xmm1 .xmm1 .xmm13] ++
    ddMul .xmm2 .xmm1 .xmm3 .xmm4 .xmm14 5 ++ [.vmovdquStore .l256 (at_ .rsi (32 * k)) .xmm2]

/-- The constants of `d = 5`: the masks of the groups of a load from bytes 0,
5, 6 and 11 (`ymm8` to `ymm11`), the shifts (`ymm12`), `31` (`ymm13`) and
`16` (`ymm14`). -/
def dd5Consts : List Instr :=
  yconst4 .xmm8 0x8080010080808000 0x8080020180808001 0x8080800380800302 0x8080800480800403 ++
  yconst4 .xmm9 0x8080060580808005 0x8080070680808006 0x8080800880800807 0x8080800980800908 ++
  yconst4 .xmm10 0x8080070680808006 0x8080080780808007 0x8080800980800908 0x8080800a80800a09 ++
  yconst4 .xmm11 0x80800c0b8080800b 0x80800d0c8080800c 0x8080800e80800e0d 0x8080800f80800f0e ++
  yconst4 .xmm12 0x0000000500000000 0x0000000700000002 0x0000000100000004 0x0000000300000006 ++
  yconst .xmm13 31 ++ yconst .xmm14 16

def dd5V : Prog isa :=
  .seq (.block (dd5Consts ++ [.mov32 .rcx (.imm 15)]))
    (.seq (.loop (.block (.vbroadcasti128 .xmm0 (at_ .rdi 0) :: dd5Grp .xmm8 0 ++ dd5Grp .xmm9 1 ++
        [.alu .add .rdi (.imm 10), .alu .add .rsi (.imm 64), .alu .sub .rcx (.imm 1)])) .ne)
      (.block (.alu .sub .rdi (.imm 6) :: .vbroadcasti128 .xmm0 (at_ .rdi 0) :: dd5Grp .xmm10 0 ++
        dd5Grp .xmm11 1 ++ [.vop .vzeroupper])))

def decodeDecompress1024Avx2 : Prog isa :=
  .seq (.block [.mov32 .rdx (.reg .rdx), .mov .rsi (.reg .rcx), .alu32 .cmp .rdx (.imm 5)])
    (.ite .e dd5V dd11V)

end VG.Impl.MlKem1024.X86_64
