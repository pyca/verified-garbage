import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx2

/-!
# Argon2 compression G on x86-64 with AVX-512

`vg_argon2_compress_avx512(x = rdi, y = rsi, out = rdx, scratch = rcx)`, with
the contract of `vg_argon2_compress`, for CPUs with AVX512F. `[0, 1024)` of
scratch holds R = X XOR Y, `[1024, 2048)` the block P permutes, and
`[2048, 2056)` the caller's MXCSR and `0x1FBF`, as in the AVX2 code.

* P works on two rows (or two columns) at once, in four 512-bit registers:
  each 256-bit half of `zmm0`–`zmm3` holds the sixteen words of one row (or
  column) as the AVX2 code's `ymm0`–`ymm3` do, quadword `q` of the half of
  register `k` being word `4k + q`. GB then acts on the eight quadwords of
  `zmm0`–`zmm3` at once, and the diagonal step rotates the quadwords of each
  half of `zmm1`, `zmm2` and `zmm3` (`vpermq`).
* `a + b + 2 · lo(a) · lo(b)` is `vpmuludq`, `vpaddq` of `a` and `b` and
  twice the product, with `zmm4` the temporary; every rotation is one
  `vprorq`.
* The permuted block is kept in scratch by pairs of columns: the 64 bytes at
  `1024 + 256c + 64k` are register `k` of columns `2c` and `2c + 1`, the
  16-byte pieces of rows `2k`, `2k + 1` in column `2c`, then those in column
  `2c + 1`. Columns are four 64-byte loads and stores. Rows `2k` and
  `2k + 1` are four 64-byte loads of R, joined into the halves of the
  registers by `vshufi32x4`, and stored permuted, each register's middle
  lanes swapped (`vshufi32x4` with `0xd8`), to their columns. The output is
  joined from the registers of two pairs of columns (`vshufi32x4` with
  `0x88` and `0xdd`) and XORed with R.
* `vpmuludq` has MXCSR-dependent timing on some processors (see "MCDT" in
  `TCB/X86_64/Isa.lean`), so the whole computation runs with MXCSR
  `0x1FBF`, between Intel's prologue and epilogue (those of the AVX2 code),
  with the caller's value saved in `r11`. Only `rax` and `r11` of the
  general-purpose registers are written. `vzeroupper` precedes the epilogue.

Every address is a pointer plus a constant, and there are no branches.
-/

namespace VG.Impl.Argon2.X86_64.Avx512

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx2 (vreg mxcsrOff)

/-- `op dst, a, b` on 512 bits. -/
def z (op : ZBinOp) (d a b : XReg) : Instr := .zop (.zbin op d a b)

/-- `a := a + b + 2 · lo(a) · lo(b)` in each quadword, with `zmm4`. -/
def addMul (a b : XReg) : List Instr :=
  [z .vpmuludq .xmm4 a b, z .vpaddq a a b, z .vpaddq .xmm4 .xmm4 .xmm4, z .vpaddq a a .xmm4]

/-- `d := (d ^ a) >>> n` in each quadword. -/
def xorRor (d a : XReg) (n : BitVec 8) : List Instr := [z .vpxord d d a, .zop (.vprorq d d n)]

/-- GB (RFC 9106 §3.6) on each quadword of `zmm0`–`zmm3`. -/
def gb : List Instr :=
  addMul .xmm0 .xmm1 ++ xorRor .xmm3 .xmm0 32 ++ addMul .xmm2 .xmm3 ++ xorRor .xmm1 .xmm2 24 ++
  addMul .xmm0 .xmm1 ++ xorRor .xmm3 .xmm0 16 ++ addMul .xmm2 .xmm3 ++ xorRor .xmm1 .xmm2 63

/-- Rotate the quadwords of each half of `zmm1`, `zmm2`, `zmm3` by one, two
and three places, so that the diagonals are columns. -/
def diagonalize : List Instr :=
  [.zop (.vpermq .xmm1 .xmm1 0x39), .zop (.vpermq .xmm2 .xmm2 0x4e), .zop (.vpermq .xmm3 .xmm3 0x93)]

/-- Rotate them back. -/
def undiagonalize : List Instr :=
  [.zop (.vpermq .xmm1 .xmm1 0x93), .zop (.vpermq .xmm2 .xmm2 0x4e), .zop (.vpermq .xmm3 .xmm3 0x39)]

/-- P on each half of `zmm0`–`zmm3`. -/
def round : List Instr := gb ++ diagonalize ++ gb ++ undiagonalize

/-- The offset in scratch of register `k` of columns `2c` and `2c + 1`. -/
def colOff (c k : Nat) : Nat := 1024 + 256 * c + 64 * k

/-- Rows `2p` and `2p + 1` of R: words `0–7` and `8–15` of row `2p` to
`zmm4` and `zmm5`, of row `2p + 1` to `zmm6` and `zmm7`, then words `4k…4k+3`
of both rows to `zmm k`. -/
def loadRows (p : Nat) : List Instr :=
  [.vmovdqu32Load .xmm4 (at_ .rcx (256 * p)), .vmovdqu32Load .xmm5 (at_ .rcx (256 * p + 64)),
    .vmovdqu32Load .xmm6 (at_ .rcx (256 * p + 128)), .vmovdqu32Load .xmm7 (at_ .rcx (256 * p + 192)),
    .zop (.vshufi32x4 .xmm0 .xmm4 .xmm6 0x44), .zop (.vshufi32x4 .xmm1 .xmm4 .xmm6 0xee),
    .zop (.vshufi32x4 .xmm2 .xmm5 .xmm7 0x44), .zop (.vshufi32x4 .xmm3 .xmm5 .xmm7 0xee)]

/-- Store register `k` of rows `2p`, `2p + 1` to columns `2k`, `2k + 1`. -/
def storeRows (p : Nat) : List Instr :=
  (List.range 4).flatMap fun k =>
    [.zop (.vshufi32x4 .xmm4 (vreg k) (vreg k) 0xd8), .vmovdqu32Store (at_ .rcx (colOff k p)) .xmm4]

def loadCols (c : Nat) : List Instr :=
  (List.range 4).map fun k => .vmovdqu32Load (vreg k) (at_ .rcx (colOff c k))

def storeCols (c : Nat) : List Instr :=
  (List.range 4).map fun k => .vmovdqu32Store (at_ .rcx (colOff c k)) (vreg k)

def rows (p : Nat) : Prog isa := .block (loadRows p ++ round ++ storeRows p)

def cols (c : Nat) : Prog isa := .block (loadCols c ++ round ++ storeCols c)

/-- 64 bytes of X XOR Y, at offset `64k`, to R. -/
def initChunk (k : Nat) : List Instr :=
  [.vmovdqu32Load .xmm0 (at_ .rdi (64 * k)), .vmovdqu32Load .xmm1 (at_ .rsi (64 * k)),
    z .vpxord .xmm0 .xmm0 .xmm1, .vmovdqu32Store (at_ .rcx (64 * k)) .xmm0]

/-- Words `8n…8n+7` of rows `2k` and `2k + 1` of the output: the permuted
block, joined from columns `4n…4n+3`, XOR R. -/
def finishChunk (n k : Nat) : List Instr :=
  [.vmovdqu32Load .xmm0 (at_ .rcx (colOff (2 * n) k)),
    .vmovdqu32Load .xmm1 (at_ .rcx (colOff (2 * n + 1) k)),
    .vmovdqu32Load .xmm4 (at_ .rcx (256 * k + 64 * n)),
    .vmovdqu32Load .xmm5 (at_ .rcx (256 * k + 128 + 64 * n)),
    .zop (.vshufi32x4 .xmm2 .xmm0 .xmm1 0x88), .zop (.vshufi32x4 .xmm3 .xmm0 .xmm1 0xdd),
    z .vpxord .xmm2 .xmm2 .xmm4, z .vpxord .xmm3 .xmm3 .xmm5,
    .vmovdqu32Store (at_ .rdx (256 * k + 64 * n)) .xmm2,
    .vmovdqu32Store (at_ .rdx (256 * k + 128 + 64 * n)) .xmm3]

def rowPass : Prog isa := (List.range 4).foldr (fun p rest => .seq (rows p) rest) (.block [])

def colPass : Prog isa := (List.range 4).foldr (fun c rest => .seq (cols c) rest) (.block [])

/-- The eight output chunks, `finishChunk n k` for `n < 2` and `k < 4`. -/
def finish : List Instr := (List.range 8).flatMap fun i => finishChunk (i / 4) (i % 4)

/-- G with MXCSR `0x1FBF`. -/
def body : Prog isa :=
  .seq (.block ((List.range 16).flatMap initChunk)) <|
  .seq rowPass <| .seq colPass <|
  .block (finish ++ [.vop .vzeroupper])

/-- `body` between Intel's MXCSR prologue and epilogue, those of the AVX2
code. -/
def compress : Prog isa :=
  .seq (.block [.stmxcsr (at_ .rcx mxcsrOff), .mov32 .r11 (.mem (at_ .rcx mxcsrOff)),
      .alu32 .and .r11 (.imm 0xFFFF)])
    (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rcx (mxcsrOff + 4)) .rax,
        .ldmxcsr (at_ .rcx (mxcsrOff + 4)), .lfence]) (.seq body (.block [.lfence])))
      (.block [.store32 (at_ .rcx mxcsrOff) .r11, .ldmxcsr (at_ .rcx mxcsrOff)]))

end VG.Impl.Argon2.X86_64.Avx512
