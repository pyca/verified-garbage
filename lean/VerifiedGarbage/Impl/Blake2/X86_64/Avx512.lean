import VerifiedGarbage.Impl.Blake2.X86_64.Avx2

/-!
# BLAKE2b compression function on x86-64 with AVX-512 (AVX512VL)

`vg_blake2b_compress_avx512(state = rdi, blocks = rsi, n = rdx, t = rcx, last = r8, scratch = r9)`,
with the contract of `vg_blake2b_compress`, for CPUs with AVX, AVX2, AVX512F
and AVX512VL. It does not use `scratch`.

The AVX2 code (`Impl/Blake2/X86_64/Avx2.lean`), whose message gathering,
diagonalization, work vector, finish and loop this code shares, with each
rotation of `G` (by 32, 24, 16 and 63) one `vprorq` on the `ymm` row (its
EVEX.256 form, AVX512F and AVX512VL) after the `vpxor`. That shortens the
rotation by 63 on the critical path, and frees `ymm14`, `ymm15` (no
`vpshufb` masks) and `ymm4`.

Every address is `rdi` or `rsi` plus a constant, and the only branches are
on `last` and on the count of blocks, so only the pointers, `n`, `t` and
`last` can affect timing. Of the general-purpose registers, only `rax`,
`rcx`, `rdx`, `rsi` and `r8` are written; `vzeroupper` ends the function.
-/

namespace VG.Impl.Blake2.X86_64.Avx512

open VG.X86_64
open VG.Impl.Blake2.X86_64.Avx2 (v)

/-- `d := (d ^ a) >>> n` in each quadword. -/
def xorRor (d a : XReg) (n : BitVec 8) : List Instr :=
  [v .vpxor d d a, .vop (.vprorq .l256 d d n)]

/-- The first half of `G` on each quadword, with the message words in `ymm5`:
`a += b + x; d = (d ^ a) >>> 32; c += d; b = (b ^ c) >>> 24`. -/
def half1 : List Instr :=
  [v .vpaddq .xmm0 .xmm0 .xmm5, v .vpaddq .xmm0 .xmm0 .xmm1] ++ xorRor .xmm3 .xmm0 32 ++
    [v .vpaddq .xmm2 .xmm2 .xmm3] ++ xorRor .xmm1 .xmm2 24

/-- The second half: `a += b + y; d = (d ^ a) >>> 16; c += d; b = (b ^ c) >>> 63`. -/
def half2 : List Instr :=
  [v .vpaddq .xmm0 .xmm0 .xmm5, v .vpaddq .xmm0 .xmm0 .xmm1] ++ xorRor .xmm3 .xmm0 16 ++
    [v .vpaddq .xmm2 .xmm2 .xmm3] ++ xorRor .xmm1 .xmm2 63

/-- Round `r` (RFC 7693 §3.2). -/
def round (r : Nat) : Prog isa :=
  .seq (.block (Avx2.msg r 0)) <| .seq (.block half1) <| .seq (.block (Avx2.msg r 1)) <|
  .seq (.block (half2 ++ Avx2.diagonalize)) <|
  .seq (.block (Avx2.msg r 2)) <| .seq (.block half1) <| .seq (.block (Avx2.msg r 3)) <|
  .block (half2 ++ Avx2.undiagonalize)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round n)

def body : Prog isa :=
  .seq (.block Avx2.init) (.seq (rounds 12) (.block (Avx2.finish ++ Avx2.advance)))

/-- `last` as a 32-bit value (whose upper half is unspecified; first, so
that the constant-time analysis knows it is public), the IV, the high word of
the counter (0), and `last` tested. -/
def setup : List Instr :=
  ([.mov32 .r8 (.reg .r8)] : List Instr) ++
    Avx2.quad .xmm11 Spec.Blake2.b.IV[0] Spec.Blake2.b.IV[1] Spec.Blake2.b.IV[2]
      Spec.Blake2.b.IV[3] ++
    Avx2.quad .xmm12 Spec.Blake2.b.IV[4] Spec.Blake2.b.IV[5] Spec.Blake2.b.IV[6]
      Spec.Blake2.b.IV[7] ++
    ([.mov32 .rax (.imm 0), .alu .test .r8 (.reg .r8)] : List Instr)

def compress : Prog isa :=
  .seq (.block setup) (.seq Avx2.flag
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block [.vop .vzeroupper])))

end VG.Impl.Blake2.X86_64.Avx512
