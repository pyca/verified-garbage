module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

/-!
# ChaCha20 keystream XOR with the data's first bytes from another buffer: x86-64 with AVX-512

`vg_chacha20_xor_split_avx512(state = rdi, src = rsi, src_len = rdx,
dst = rcx, len = r8, buf = r9)`, with the contract of
`vg_chacha20_xor_split`, for CPUs with AVX-512F: the keystream XORed into
the `len` bytes made of the `src_len` bytes at `src` and the bytes at `dst`
after them, written to `dst`.

It is `vg_chacha20_xor_avx512` (`Avx512.xor`) on `dst`, except that each
block of 64 bytes of the input that lies within the first `C` bytes is
loaded from `src` instead (`selXor`): the sixteen-block loop (`bodySel`)
and the last pass of 513 to 1023 bytes (`last16Sel`) compare `r10`, the
number of those bytes from the block their pass starts at (`C` less the
bytes before it, but at least 0), with the end of each block, and load it
from `r8`, the same offset in `src`, if it is within them, else from `dst`.
Fewer than 513 bytes after the loop are XORed in place, by a call of
`vg_chacha20_xor_avx512`. Before, the bytes of `src` from `C` on, fewer than
64 (or fewer than 1024 if those last bytes are XORed in place), are copied
to `dst` (`SealGather.copyBytes`),
where `C` is `src_len` rounded down to a multiple of 64, or, if fewer than
513 bytes follow the loop, the smaller of that and `len` rounded down to a
multiple of 1024 (`entry`).

So a TLS record, its payload in `src` and its content type copied after it
in `dst`, is encrypted by one pass over the keystream, with no copy of the
payload but its last block's bytes.

`len` waits in `rbx` during the copy, and `rbx` in `buf`. The branches are on `src_len` and
`len` only, and every address is a pointer plus a constant or a function
of the lengths, so only the pointers and the lengths can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64.Avx512

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- XOR the 64 bytes of keystream in `x` into the block of the input at
offset `off` (through `t`), written to the data at `rsi + off`: the input
from `src` at `r8 + off` if the block ends within the first `r10` bytes, else
from the data. -/
def selXor (x t : XReg) (off : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .r10 (.imm (BitVec.ofNat 32 (off + 64)))])
    (.ite .b (.block [.vmovdqu32Load t (at_ .rsi off), z .vpxord t t x, .vmovdqu32Store (at_ .rsi off) t])
      (.block [.vmovdqu32Load t (at_ .r8 off), z .vpxord t t x, .vmovdqu32Store (at_ .rsi off) t]))

/-- Straight-line code, or a `selXor`. -/
inductive Piece where
  | ins (is : List Instr)
  | sel (x t : XReg) (off : Nat)

def Piece.prog : Piece → Prog isa
  | .ins is => .block is
  | .sel x t off => selXor x t off

/-- The pieces one after the other. -/
def pieces : List Piece → Prog isa
  | [] => .block []
  | p :: ps => .seq p.prog (pieces ps)

/-- The shuffles of `gather` (blocks `i, i + 4, i + 8, i + 12` into
`b, d, t0, t1`). -/
def shuffles (a b c d t0 t1 : XReg) : List Instr :=
  [.zop (.vshufi32x4 t0 a b 0x44), .zop (.vshufi32x4 a a b 0xee),
   .zop (.vshufi32x4 t1 c d 0x44), .zop (.vshufi32x4 c c d 0xee),
   .zop (.vshufi32x4 b t0 t1 0x88), .zop (.vshufi32x4 d t0 t1 0xdd),
   .zop (.vshufi32x4 t0 a c 0x88), .zop (.vshufi32x4 t1 a c 0xdd)]

/-- `gather`, each block by `selXor`. -/
def gatherSel (i : Nat) (a b c d t0 t1 : XReg) : List Piece :=
  [.ins (shuffles a b c d t0 t1), .sel b a (64 * i), .sel d a (64 * (i + 4)),
   .sel t0 a (64 * (i + 8)), .sel t1 a (64 * (i + 12))]

/-- `finish` before its gathers: the rows added and transposed. -/
def finishRows : List Instr :=
  ([.vmovdqu32Store (at_ .rcx save0Off) .xmm14, .vmovdqu32Store (at_ .rcx save1Off) .xmm15] : List Instr) ++
  addRow 0 [.xmm0, .xmm1, .xmm2, .xmm3] ++
    transpose .xmm0 .xmm1 .xmm2 .xmm3 .xmm14 .xmm15 ++
  addRow 1 [.xmm4, .xmm5, .xmm6, .xmm7] ++
    transpose .xmm4 .xmm5 .xmm6 .xmm7 .xmm1 .xmm15 ++
  addRow 2 [.xmm8, .xmm9, .xmm10, .xmm11] ++
    transpose .xmm8 .xmm9 .xmm10 .xmm11 .xmm5 .xmm15 ++
  ([.vmovdqu32Load .xmm9 (at_ .rcx save0Off), .vmovdqu32Load .xmm15 (at_ .rcx save1Off),
   .vmovdqu32Store (at_ .rcx save0Off) .xmm2, .vmovdqu32Store (at_ .rcx save1Off) .xmm3] : List Instr) ++
  addRow 3 [.xmm12, .xmm13, .xmm9, .xmm15] ++
    ([.vmovdqu32Load .xmm3 (at_ .rcx incOff), z .vpaddd .xmm12 .xmm12 .xmm3] : List Instr) ++
    transpose .xmm12 .xmm13 .xmm9 .xmm15 .xmm2 .xmm3

/-- `finish`, each block by `selXor`. -/
def finishSel : List Piece :=
  [.ins finishRows] ++
  gatherSel 0 .xmm0 .xmm4 .xmm8 .xmm12 .xmm13 .xmm3 ++
  gatherSel 1 .xmm14 .xmm1 .xmm5 .xmm2 .xmm13 .xmm3 ++
  [.ins [.vmovdqu32Load .xmm0 (at_ .rcx save0Off)]] ++ gatherSel 2 .xmm0 .xmm6 .xmm10 .xmm9 .xmm13 .xmm3 ++
  [.ins [.vmovdqu32Load .xmm0 (at_ .rcx save1Off)]] ++ gatherSel 3 .xmm0 .xmm7 .xmm11 .xmm15 .xmm13 .xmm3

/-- `r10` less `n`, but at least 0 (through `rax`). -/
def subSat (n : Nat) : List Instr :=
  [.mov32 .rax (.imm 0), .alu .sub .r10 (.imm (BitVec.ofNat 32 n)), .cmov .b .r10 (.reg .rax)]

/-- `next`, advancing the input in `src` and `r10` first. -/
def nextSel : List Instr := [.alu .add .r8 (.imm 1024)] ++ subSat 1024 ++ next

/-- Sixteen blocks. -/
def bodySel : Prog isa := .seq (.block setup) (.seq (rounds 10) (.seq (pieces finishSel) (.block nextSel)))

/-! ## The last pass, of 513 to 1023 bytes -/

/-- As `gatherH`, each block by `selXor`. -/
def gatherHSel (i : Nat) (a b c d t0 t1 : XReg) : List Piece :=
  [.ins (shuffles a b c d t0 t1), .sel b a (64 * i), .sel d a (64 * (i + 4))]

/-- `finishP` before its gathers. -/
def finishPRows : List Instr :=
  ([.vmovdqu32Store (at_ .r9 save0Off) .xmm14, .vmovdqu32Store (at_ .r9 save1Off) .xmm15] : List Instr) ++
  addRow 0 [.xmm0, .xmm1, .xmm2, .xmm3] ++
    transpose .xmm0 .xmm1 .xmm2 .xmm3 .xmm14 .xmm15 ++
  addRow 1 [.xmm4, .xmm5, .xmm6, .xmm7] ++
    transpose .xmm4 .xmm5 .xmm6 .xmm7 .xmm1 .xmm15 ++
  addRow 2 [.xmm8, .xmm9, .xmm10, .xmm11] ++
    transpose .xmm8 .xmm9 .xmm10 .xmm11 .xmm5 .xmm15 ++
  ([.vmovdqu32Load .xmm9 (at_ .r9 save0Off), .vmovdqu32Load .xmm15 (at_ .r9 save1Off),
   .vmovdqu32Store (at_ .r9 save0Off) .xmm2, .vmovdqu32Store (at_ .r9 save1Off) .xmm3] : List Instr) ++
  addRow 3 [.xmm12, .xmm13, .xmm9, .xmm15] ++
    ([.vmovdqu32Load .xmm3 (at_ .r9 incOff), z .vpaddd .xmm12 .xmm12 .xmm3] : List Instr) ++
    transpose .xmm12 .xmm13 .xmm9 .xmm15 .xmm2 .xmm3

/-- `finishP`, each block by `selXor`. -/
def finishPSel : List Piece :=
  [.ins finishPRows] ++
  gatherHSel 0 .xmm0 .xmm4 .xmm8 .xmm12 .xmm13 .xmm3 ++
  gatherHSel 1 .xmm14 .xmm1 .xmm5 .xmm2 .xmm0 .xmm8 ++
  [.ins [.vmovdqu32Load .xmm4 (at_ .r9 save0Off)]] ++ gatherHSel 2 .xmm4 .xmm6 .xmm10 .xmm9 .xmm12 .xmm14 ++
  [.ins [.vmovdqu32Load .xmm4 (at_ .r9 save1Off)]] ++ gatherHSel 3 .xmm4 .xmm7 .xmm11 .xmm15 .xmm5 .xmm1

/-- As `adv512`, advancing the input in `src` and `r10` too. -/
def adv512Sel : List Instr := adv512 ++ [.alu .add .r8 (.imm 512)] ++ subSat 512

/-- As `cond`, the block by `selXor`. -/
def condSel (j : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 (64 * j + 64)))])
    (.ite .b (.block [.vmovdqu32Store (at_ .r9 0) (blkReg (8 + j))]) (selXor (blkReg (8 + j)) .xmm2 (64 * j)))

def condsSel : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (condSel n) (condsSel n)

/-- As `last16`, each block by `selXor`. -/
def last16Sel : Prog isa :=
  .seq (.block (.mov .r9 (.reg .rcx) :: setupB .r9)) (.seq (rounds 10) (.seq (pieces finishPSel)
    (.seq (.block adv512Sel) (.seq (condsSel 8) (.seq (.block adv) (.seq Avx512Tail.fromBuf
      (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])))))))

/-! ## The function -/

/-- `C` in `r10`: `src_len` rounded down to a multiple of 64, and, unless
513 or more bytes follow the whole 1024-byte passes (`r11`), at most `len`
rounded down to a multiple of 1024 (`rax`). -/
def entryC : Prog isa :=
  .seq (.block [.mov .rax (.reg .r8), .shift .shr .rax 10, .shift .shl .rax 10,
    .mov .r10 (.reg .rdx), .shift .shr .r10 6, .shift .shl .r10 6,
    .mov .r11 (.reg .r8), .alu .sub .r11 (.reg .rax), .alu .cmp .r11 (.imm 513)])
  (.ite .b (.block [.alu .cmp .r10 (.reg .rax), .cmov .ae .r10 (.reg .rax)]) (.block []))

/-- The copy's arguments: the bytes of `src` from `C` on to `dst + C`, the
state kept in `r11`, `C` in `rdx` and `len` in `rbx`, whose value waits in
`buf`. -/
def copyArgs : List Instr :=
  [.store (at_ .r9 0) .rbx, .mov .rbx (.reg .r8), .mov .r11 (.reg .rdi), .mov .rdi (.reg .rcx),
   .alu .add .rdi (.reg .r10), .alu .add .rsi (.reg .r10), .mov .rcx (.reg .rdx), .alu .sub .rcx (.reg .r10),
   .mov .rdx (.reg .r10)]

/-- The loop's registers: the state, the data (`dst`), its length, `buf`,
`src` in `r8` and `C` in `r10`; `rbx` back from `buf`. -/
def loopArgs : List Instr :=
  [.mov .rax (.mem (at_ .r9 0)), .mov .r8 (.reg .rsi), .alu .sub .r8 (.reg .rdx), .mov .rsi (.reg .rdi),
   .alu .sub .rsi (.reg .rdx), .mov .r10 (.reg .rdx), .mov .rdx (.reg .rbx), .mov .rbx (.reg .rax),
   .mov .rdi (.reg .r11), .mov .rcx (.reg .r9)]

def xorSplit : Prog isa :=
  .seq entryC
  (.seq (.block copyArgs)
  (.seq (ChaCha20Poly1305.X86_64.SealGather.copyBytes .z64)
  (.seq (.block (loopArgs ++ Avx512Tail.consts ++ consts ++ ([.alu .cmp .rdx (.imm 1024)] : List Instr)))
  (.seq (.ite .b (.block []) (.loop bodySel .ae))
  (.seq (.block [.alu .cmp .rdx (.imm 513)]) (.ite .b (.call "vg_chacha20_xor_avx512" xor) last16Sel))))))

end VG.Impl.ChaCha20.X86_64.Avx512
