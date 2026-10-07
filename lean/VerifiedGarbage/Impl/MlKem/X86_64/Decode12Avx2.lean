import VerifiedGarbage.Impl.MlKem.X86_64.Encode12
import VerifiedGarbage.Impl.MlKem.X86_64.NttAvx2

/-!
# ML-KEM on x86-64: `vg_mlkem_decode12_avx2`

`decode12Avx2(b = rdi, f = rsi)` is `vg_mlkem_decode12` (`Encode12.lean`)
on eight coefficients at a time, from 12 bytes, in the doublewords of an
AVX2 register, as `vg_mlkem_sample_ntt4_avx2` computes its candidates
(`Sample4.vcand`): `vbroadcasti128` loads 16 bytes into both lanes,
`vpshufb` puts bytes `3i, 3i+1` (for the first value of a pair) or
`3i+1, 3i+2` (for the second) of the 12 in the low half of each
doubleword, bytes 0 to 5 in the low lane and 6 to 11 in the high one
(`ymm8`), `vpsrlvd` shifts the second values right by 4 (`ymm9`), and
`vpand` keeps their low 12 bits (`ymm10`). Each value `x < 2¹²` is then
reduced modulo `q` (`ymm11`) without a branch: `x - q` is negative exactly
when `x < q`, and `vpsrad` by 31 turns its sign into a mask of `q` to add
back. The eight are stored to `f`.

The loop runs over the first 31 groups of 12 bytes, with `rcx` counting
down. A load of the last group would read 4 bytes past `b`, so the code
loads it from 4 bytes before it, with a mask that takes bytes 4 to 15
instead (`ymm12`). The constants are built in registers, through `rax`,
`ymm0` and `ymm1`. There are no multiplications. It clears the upper
halves of the vector registers before returning (`vzeroupper`), for the
SSE code its callers run next. Every address and branch depends only on
the pointers.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `ymm r` set to the quadwords `q₀, q₁, q₂, q₃` (from the lowest), through `rax`, `ymm0` and `ymm1`. -/
def yconst4 (r : XReg) (q₀ q₁ q₂ q₃ : BitVec 64) : List Instr :=
  [.movImm64 .rax q₀, .vop (.vmovq r .rax), .movImm64 .rax q₁, .vop (.vmovq .xmm0 .rax),
    .vop (.vbin .vpunpcklqdq .l128 r r .xmm0), .movImm64 .rax q₂, .vop (.vmovq .xmm0 .rax), .movImm64 .rax q₃,
    .vop (.vmovq .xmm1 .rax), .vop (.vbin .vpunpcklqdq .l128 .xmm0 .xmm0 .xmm1), .vop (.vinserti128 r r .xmm0 1)]

/-- The constants: the masks of `vpshufb` (`ymm8`, and `ymm12` for the last
group), the shifts (`ymm9`), `0xfff` (`ymm10`) and `q` (`ymm11`). -/
def d12Consts : List Instr :=
  yconst4 .xmm8 0x8080020180800100 0x8080050480800403 0x8080080780800706 0x80800b0a80800a09 ++
    yconst4 .xmm12 0x8080060580800504 0x8080090880800807 0x80800c0b80800b0a 0x80800f0e80800e0d ++
    [.movImm64 .rax 0x0000000400000000, .vop (.vmovq .xmm9 .rax), .vop (.vpbroadcastq .l256 .xmm9 .xmm9)] ++
    yconst .xmm10 0xfff ++ yconst .xmm11 3329

/-- The eight coefficients of the 12 bytes that the mask `m` selects from
the 16 at `rdi`, reduced, to `rsi`. -/
def d12Body (m : XReg) : List Instr :=
  [.vbroadcasti128 .xmm0 (at_ .rdi 0), yb .vpshufb .xmm0 .xmm0 m, .vop (.vvar .vpsrlvd .l256 .xmm0 .xmm0 .xmm9),
    yb .vpand .xmm0 .xmm0 .xmm10, yb .vpsubd .xmm0 .xmm0 .xmm11, .vop (.vshift .psrad .l256 .xmm1 .xmm0 31),
    yb .vpand .xmm1 .xmm1 .xmm11, yb .vpaddd .xmm0 .xmm0 .xmm1, .vmovdquStore .l256 (at_ .rsi 0) .xmm0]

def d12Step : List Instr := [.alu .add .rdi (.imm 12), .alu .add .rsi (.imm 32), .alu .sub .rcx (.imm 1)]

def decode12Avx2 : Prog isa :=
  .seq (.block (d12Consts ++ [.mov32 .rcx (.imm 31)]))
    (.seq (.loop (.block (d12Body .xmm8 ++ d12Step)) .ne)
      (.block (.alu .sub .rdi (.imm 4) :: d12Body .xmm12 ++ [.vop .vzeroupper])))

end VG.Impl.MlKem.X86_64
