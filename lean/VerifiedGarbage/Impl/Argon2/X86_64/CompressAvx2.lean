module

public import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-!
# Argon2 compression G on x86-64 with AVX2

`vg_argon2_compress_avx2(x = rdi, y = rsi, out = rdx, scratch = rcx)`, with
the contract of `vg_argon2_compress`, for CPUs with AVX and AVX2. As in the
scalar code, `[0, 1024)` of scratch holds R = X XOR Y and `[1024, 2048)` the
block P permutes; `[2048, 2056)` holds the caller's MXCSR and `0x1FBF`.

* P works on the sixteen words of a row or a column in four AVX registers:
  `ymm0`–`ymm3` hold its words `0–3`, `4–7`, `8–11` and `12–15`, quadword
  `q` of the register holding words `4k…4k+3` being word `4k + q`. GB then
  acts on the four quadwords of `ymm0`–`ymm3` at once: the four column GBs of
  P are one GB on the registers, and the diagonal ones are another, after
  the quadwords of `ymm1`, `ymm2` and `ymm3` are rotated by one, two and
  three places (`vpermq`), which are rotated back after it.
* `a + b + 2 · lo(a) · lo(b)` is `vpmuludq` (the products of the low
  halves), `vpaddq` of `a` and `b` and twice the product; `ymm4` is the
  temporary. A rotation by 32 is a `vpshufd` of the doublewords of each
  quadword; one by 24 or 16 a `vpshufb` of its bytes, with the masks in
  `ymm14` and `ymm15`; one by 63 the quadword shifted right by 63, XORed with
  the quadword added to itself.
* A row is four consecutive 32-byte loads and stores. Column `j` is words
  `2j, 2j + 1` of each row: the words of register `k` are those of rows
  `2k` and `2k + 1`, two 16-byte loads joined by `vinserti128` (and split
  by `vextracti128` to store them back).
* `vpmuludq` has MXCSR-dependent timing on some processors (see "MCDT" in
  `TCB/X86_64/Isa.lean`), so the whole computation runs with MXCSR
  `0x1FBF`, between Intel's prologue and epilogue, with the caller's value
  saved in `r11`. Only `rax` and `r11` of the general-purpose registers are
  written. `vzeroupper` precedes the epilogue.

Every address is a pointer plus a constant, and there are no branches.
-/

@[expose] public section

namespace VG.Impl.Argon2.X86_64.Avx2

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

/-- `op dst, a, b` on 256 bits. -/
def v (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

/-- The register holding words `4k…4k+3` of the row or column. -/
def vreg : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | _ => .xmm3

/-- The masks of the rotations right by 24 and by 16 (`vpshufb`): byte `i`
of each quadword is byte `i + 3` (respectively `i + 2`) modulo 8 of it. -/
def rot24Lo : BitVec 64 := 0x0201000706050403
def rot24Hi : BitVec 64 := 0x0a09080f0e0d0c0b
def rot16Lo : BitVec 64 := 0x0100070605040302
def rot16Hi : BitVec 64 := 0x09080f0e0d0c0b0a

/-- `d := lo` in quadwords 0 and 2 and `hi` in 1 and 3, through `rax` and
`ymm13`. -/
def mask (d : XReg) (lo hi : BitVec 64) : List Instr :=
  [.movImm64 .rax lo, .vop (.vmovq d .rax), .movImm64 .rax hi, .vop (.vmovq .xmm13 .rax),
    .vop (.vbin .vpunpcklqdq .l128 d d .xmm13), .vop (.vpermq d d 0x44)]

def masks : List Instr := mask .xmm14 rot24Lo rot24Hi ++ mask .xmm15 rot16Lo rot16Hi

/-- `a := a + b + 2 · lo(a) · lo(b)` in each quadword, with `ymm4`. -/
def addMul (a b : XReg) : List Instr :=
  [v .vpmuludq .xmm4 a b, v .vpaddq a a b, v .vpaddq .xmm4 .xmm4 .xmm4, v .vpaddq a a .xmm4]

/-- `d := (d ^ a) >>> 32` in each quadword. -/
def xorRot32 (d a : XReg) : List Instr := [v .vpxor d d a, .vop (.vpshufd .l256 d d 0xb1)]

/-- `d := (d ^ a) >>> 24` in each quadword. -/
def xorRot24 (d a : XReg) : List Instr := [v .vpxor d d a, v .vpshufb d d .xmm14]

/-- `d := (d ^ a) >>> 16` in each quadword. -/
def xorRot16 (d a : XReg) : List Instr := [v .vpxor d d a, v .vpshufb d d .xmm15]

/-- `d := (d ^ a) >>> 63` in each quadword, with `ymm4`. -/
def xorRot63 (d a : XReg) : List Instr :=
  [v .vpxor d d a, .vop (.vshift .psrlq .l256 .xmm4 d 63), v .vpaddq d d d, v .vpxor d d .xmm4]

/-- GB (RFC 9106 §3.6) on each quadword of `ymm0`–`ymm3`. -/
def gb : List Instr :=
  addMul .xmm0 .xmm1 ++ xorRot32 .xmm3 .xmm0 ++ addMul .xmm2 .xmm3 ++ xorRot24 .xmm1 .xmm2 ++
  addMul .xmm0 .xmm1 ++ xorRot16 .xmm3 .xmm0 ++ addMul .xmm2 .xmm3 ++ xorRot63 .xmm1 .xmm2

/-- Rotate the quadwords of `ymm1`, `ymm2`, `ymm3` by one, two and three
places, so that the diagonals are columns. -/
def diagonalize : List Instr :=
  [.vop (.vpermq .xmm1 .xmm1 0x39), .vop (.vpermq .xmm2 .xmm2 0x4e),
    .vop (.vpermq .xmm3 .xmm3 0x93)]

/-- Rotate them back. -/
def undiagonalize : List Instr :=
  [.vop (.vpermq .xmm1 .xmm1 0x93), .vop (.vpermq .xmm2 .xmm2 0x4e),
    .vop (.vpermq .xmm3 .xmm3 0x39)]

/-- P on the sixteen words in `ymm0`–`ymm3`. -/
def round : List Instr := gb ++ diagonalize ++ gb ++ undiagonalize

/-- The offset in scratch of the 16 bytes of row `2k` (`hi = false`) or
`2k + 1` (`hi = true`) in column `j`, or of the 32 bytes of words `4k…4k+3`
of row `i`. -/
def colOff (j k : Nat) (hi : Bool) : Nat := 1024 + 256 * k + 16 * j + if hi then 128 else 0
def rowOff (i k : Nat) : Nat := 1024 + 128 * i + 32 * k

def loadRow (i : Nat) : List Instr :=
  (List.range 4).map fun k => .vmovdquLoad .l256 (vreg k) (at_ .rcx (rowOff i k))

def storeRow (i : Nat) : List Instr :=
  (List.range 4).map fun k => .vmovdquStore .l256 (at_ .rcx (rowOff i k)) (vreg k)

def loadCol (j : Nat) : List Instr :=
  (List.range 4).flatMap fun k =>
    [.vmovdquLoad .l128 (vreg k) (at_ .rcx (colOff j k false)),
      .vmovdquLoad .l128 .xmm4 (at_ .rcx (colOff j k true)),
      .vop (.vinserti128 (vreg k) (vreg k) .xmm4 1)]

def storeCol (j : Nat) : List Instr :=
  (List.range 4).flatMap fun k =>
    [.vmovdquStore .l128 (at_ .rcx (colOff j k false)) (vreg k),
      .vop (.vextracti128 .xmm4 (vreg k) 1),
      .vmovdquStore .l128 (at_ .rcx (colOff j k true)) .xmm4]

def row (i : Nat) : Prog isa := .block (loadRow i ++ round ++ storeRow i)

def col (j : Nat) : Prog isa := .block (loadCol j ++ round ++ storeCol j)

/-- 32 bytes of X XOR Y, at offset `32k`, to both halves of scratch. -/
def initChunk (k : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdi (32 * k)), .vmovdquLoad .l256 .xmm1 (at_ .rsi (32 * k)),
    v .vpxor .xmm0 .xmm0 .xmm1, .vmovdquStore .l256 (at_ .rcx (32 * k)) .xmm0,
    .vmovdquStore .l256 (at_ .rcx (1024 + 32 * k)) .xmm0]

/-- 32 bytes of the output: the permuted block XOR R. -/
def finishChunk (k : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rcx (1024 + 32 * k)), .vmovdquLoad .l256 .xmm1 (at_ .rcx (32 * k)),
    v .vpxor .xmm0 .xmm0 .xmm1, .vmovdquStore .l256 (at_ .rdx (32 * k)) .xmm0]

def rows : Prog isa := (List.range 8).foldr (fun i rest => .seq (row i) rest) (.block [])

def cols : Prog isa := (List.range 8).foldr (fun j rest => .seq (col j) rest) (.block [])

/-- G with MXCSR `0x1FBF`. -/
def body : Prog isa :=
  .seq (.block (masks ++ (List.range 32).flatMap initChunk)) <|
  .seq rows <| .seq cols <|
  .block ((List.range 32).flatMap finishChunk ++ ([.vop .vzeroupper] : List Instr))

/-- The offset in scratch of the caller's MXCSR; `0x1FBF` is 4 bytes above. -/
def mxcsrOff : Nat := 2048

/-- `body` between Intel's MXCSR prologue and epilogue, the caller's MXCSR
saved in `r11` (with its reserved bits 31:16, which are 0, cleared). -/
def compress : Prog isa :=
  .seq (.block [.stmxcsr (at_ .rcx mxcsrOff), .mov32 .r11 (.mem (at_ .rcx mxcsrOff)),
      .alu32 .and .r11 (.imm 0xFFFF)])
    (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rcx (mxcsrOff + 4)) .rax,
        .ldmxcsr (at_ .rcx (mxcsrOff + 4)), .lfence]) (.seq body (.block [.lfence])))
      (.block [.store32 (at_ .rcx mxcsrOff) .r11, .ldmxcsr (at_ .rcx mxcsrOff)]))

end VG.Impl.Argon2.X86_64.Avx2
