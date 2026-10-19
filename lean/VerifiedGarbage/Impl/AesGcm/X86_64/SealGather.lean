module

import VerifiedGarbage.Impl.AesGcm.X86_64.StreamTo
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

/-!
# AES-GCM one-shot encryption out of place, from a list of slices: x86-64

`vg_aes_gcm_seal_gather` `(ctx = rdi, rounds = rsi, nonce = rdx,
nonce_len = rcx, aad = r8, aad_len = r9, src = [rsp + 8],
src_count = [rsp + 16], dst = [rsp + 24], len = [rsp + 32],
tag = [rsp + 40], work = [rsp + 48])`, its working space allocated on the
stack by `withStackArgScratch` (`work` is the argument the frame adds),
generic over the implementations of `vg_aes_gcm_seal`, `vg_aes_gcm_stream_init`,
`vg_aes_gcm_stream_aad`, `vg_aes_gcm_stream_encrypt_to` and
`vg_aes_gcm_stream_finish` it calls, as the other functions of AES-GCM.

A text shorter than `ts` bytes (a parameter of the code, below `2^31`) is
copied whole and sealed by `sealFn` (`copySeal`, below), after one
comparison of its length. When a longer text is shorter than `t` bytes (also
a parameter), or its first slice holds all its whole blocks (as a TLS
record's text does, followed by its content type), it takes the short path
(`copyShort`), with the arguments kept in `work`. If the first slice holds
all the whole blocks and at least `ts` bytes, the slices after it are
copied, slice after slice, to the output after its length (`copy`: 64 bytes
at a time through `xmm0`–`xmm3`, then 16, then the last 16 again, or one at
a time), and the text is encrypted by one call of `splitFn`
(`vg_aes_gcm_seal_split` for the same implementations), from the first slice
where it is and the rest in the output (`copySplit`). Otherwise all the
slices are copied, and the text is encrypted there in place by one call of
`sealFn` (`vg_aes_gcm_seal` for the same implementations, with the short path
of the AVX-512 ones; `copySeal`): sealing from the first slice would encrypt
whole blocks after it in a second pass of the blocks loop, or, below `ts`,
pay more in calls than the copy costs. The streaming functions' calls cost
more than the copy saves below `t`, and more than the few bytes copied after
a first slice holding all the whole blocks.

`vg_aes_gcm_seal_gather_prepared` first tests, from the arguments where the
caller put them, whether the text is a TLS record's (a 12-byte nonce, at most
16 bytes of additional data, one or two slices, the second ending at most 16
bytes after the first's whole blocks: `frontTest`), and if so copies the
second slice to the output after the first and seals the text by one call of
`vg_aes_gcm_seal_split_prepared` from the first slice where it is
(`frontFast`), before anything else (`withFront`).

Otherwise it runs the streaming functions on a state of its own, in `work`: it starts
the message with the nonce, absorbs the additional data, and, if there is
any text, pads the additional data with zeros to a whole block (as GHASH
does), so that `vg_aes_gcm_stream_encrypt_to` encrypts the whole blocks of
each slice straight from where it is to the output; then it encrypts the
slices one after the other, each to the output after the ones before it,
and writes the tag. The arguments and the progress through the slices are
kept in `work` across the calls.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.SealGather

open VG.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (next advance)

/-- Where the arguments and the progress are kept, in `work`. -/
def gCtx : Nat := 0
def gRounds : Nat := 8
def gAad : Nat := 16
def gAlen : Nat := 24
def gDst : Nat := 32
def gLen : Nat := 40
def gTag : Nat := 48
/-- The descriptor of the next slice. -/
def gDesc : Nat := 56
/-- The slices left. -/
def gLeft : Nat := 64
/-- The bytes of text done. -/
def gOff : Nat := 72
/-- The length of the additional data, padded once there is text. -/
def gAlenP : Nat := 80
/-- 16 zero bytes, the padding. -/
def gZero : Nat := 88
/-- The streaming state. -/
def gState : Nat := 104

/-- The register arguments, `src` and `src_count` kept; `work` in `r11`. -/
def entry1 : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .r10 (.mem (at_ .rsp 8)), .mov .rax (.mem (at_ .rsp 16)),
    .store (at_ .r11 gCtx) .rdi, .store (at_ .r11 gRounds) .rsi, .store (at_ .r11 gAad) .r8,
    .store (at_ .r11 gAlen) .r9, .store (at_ .r11 gAlenP) .r9, .store (at_ .r11 gDesc) .r10,
    .store (at_ .r11 gLeft) .rax]

/-- `dst`, `len` and `tag` kept, no text done, the padding zero, and the
arguments of `vg_aes_gcm_stream_init(ctx, nonce, nonce_len, state)`. -/
def entry2 : List Instr :=
  [.mov .rax (.mem (at_ .rsp 24)), .mov .r10 (.mem (at_ .rsp 32)), .mov .r8 (.mem (at_ .rsp 40)),
    .store (at_ .r11 gDst) .rax, .store (at_ .r11 gLen) .r10, .store (at_ .r11 gTag) .r8,
    .mov32 .rax (imm 0), .store (at_ .r11 gOff) .rax, .store (at_ .r11 gZero) .rax,
    .store (at_ .r11 (gZero + 8)) .rax, .mov .rsi (.reg .rdx), .mov .rdx (.reg .rcx), .mov .rcx (.reg .r11),
    .alu .add .rcx (imm gState)]

/-- The arguments of `vg_aes_gcm_stream_aad(ctx, state, 0, aad, aad_len)`. -/
def aadArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .rdi (.mem (at_ .r11 gCtx)), .mov .rsi (.reg .r11),
    .alu .add .rsi (imm gState), .mov32 .rdx (imm 0), .mov .rcx (.mem (at_ .r11 gAad)),
    .mov .r8 (.mem (at_ .r11 gAlen))]

/-- The length of the text, `ZF` if 0. -/
def textLen : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .rax (.mem (at_ .r11 gLen)), .alu .test .rax (.reg .rax)]

/-- `aad_len` into `rcx`, and its remainder modulo 16 into `r8`, `ZF` if 0. -/
def padLen : List Instr :=
  [.mov .rcx (.mem (at_ .r11 gAlen)), .mov .r8 (.reg .rcx), .alu .and .r8 (imm 15), .alu .test .r8 (.reg .r8)]

/-- The padded length kept, and the arguments of
`vg_aes_gcm_stream_aad(ctx, state, aad_len, zeros, 16 - aad_len % 16)`. -/
def padArgs : List Instr :=
  [.mov32 .rax (imm 16), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax), .mov .rdi (.mem (at_ .r11 gCtx)),
    .mov .rax (.reg .rcx), .alu .add .rax (.reg .r8), .store (at_ .r11 gAlenP) .rax,
    .mov .rsi (.reg .r11), .alu .add .rsi (imm gState), .mov .rdx (.reg .rcx), .mov .rcx (.reg .r11),
    .alu .add .rcx (imm gZero)]

/-- The slices left, `ZF` if none. -/
def leftTest : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .rax (.mem (at_ .r11 gLeft)), .alu .test .rax (.reg .rax)]

/-- The arguments of `vg_aes_gcm_stream_encrypt_to(ctx, rounds, state,
aad_len, off, src_i, len_i, dst + off, len_i)` for the next slice, with its
length in `rax` and `dst + off` in `r10`. -/
def sliceArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .r10 (.mem (at_ .r11 gDesc)), .mov .r9 (.mem (at_ .r10 0)),
    .mov .rax (.mem (at_ .r10 8)), .mov .r10 (.mem (at_ .r11 gDst)), .mov .rcx (.mem (at_ .r11 gOff)),
    .alu .add .r10 (.reg .rcx), .mov .rdi (.mem (at_ .r11 gCtx)), .mov .rsi (.mem (at_ .r11 gRounds)),
    .mov .rdx (.reg .r11), .alu .add .rdx (imm gState), .mov .rcx (.mem (at_ .r11 gAlenP)),
    .mov .r8 (.mem (at_ .r11 gOff))]

/-- Past the slice: the bytes done and the descriptor advance, one slice
fewer is left, `ZF` if none. -/
def sliceNext : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .r10 (.mem (at_ .r11 gDesc)), .mov .rax (.mem (at_ .r10 8)),
    .mov .rcx (.mem (at_ .r11 gOff)), .alu .add .rcx (.reg .rax), .alu .add .r10 (imm 16),
    .mov .rax (.mem (at_ .r11 gLeft)), .alu .sub .rax (imm 1), .store (at_ .r11 gOff) .rcx,
    .store (at_ .r11 gDesc) .r10, .store (at_ .r11 gLeft) .rax, .alu .test .rax (.reg .rax)]

/-- The arguments of `vg_aes_gcm_stream_finish(ctx, rounds, state, aad_len,
len, tag)`. -/
def finArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .rdi (.mem (at_ .r11 gCtx)), .mov .rsi (.mem (at_ .r11 gRounds)),
    .mov .rdx (.reg .r11), .alu .add .rdx (imm gState), .mov .rcx (.mem (at_ .r11 gAlen)),
    .mov .r8 (.mem (at_ .r11 gLen)), .mov .r9 (.mem (at_ .r11 gTag))]

/-- The slices, one after the other, by `encTo` (`vg_aes_gcm_stream_encrypt_to`),
with `len_i`, `dst + off` and `len_i` passed on the stack. -/
def slices (encTo : Fn) : Prog isa :=
  .seq (.block leftTest)
    (.ite .e (.block [])
      (.loop (.seq (.block sliceArgs)
        (.seq (.frame (.push [.rax, .r10, .rax]) (.call encTo.name encTo.code) (.pop .rax 3))
          (.block sliceNext))) .ne))

/-- If there is any text: the additional data padded to a whole block, by
`aad` (`vg_aes_gcm_stream_aad`), then the slices. -/
def text (aad encTo : Fn) : Prog isa :=
  .seq (.block textLen)
    (.ite .e (.block [])
      (.seq (.block padLen)
        (.seq (.ite .e (.block []) (.seq (.block padArgs) (.call aad.name aad.code)))
          (slices encTo))))

/-! ## A short text: copied, then sealed in place -/

/-- The nonce and its length, which `entry2` moved to `rsi` and `rdx`, kept
in the streaming state's slots, which this path does not use; then the slices
left (all of them) in `r9`, `dst` in `rdi` and the first descriptor in `r11`. -/
def copyEntry : List Instr :=
  [.store (at_ .r11 gState) .rsi, .store (at_ .r11 (gState + 8)) .rdx, .mov .r9 (.mem (at_ .r11 gLeft)),
    .mov .rdi (.mem (at_ .r11 gDst)), .mov .r11 (.mem (at_ .r11 gDesc))]

/-- `[rsi + r10 + d]`, `[rdi + r10 + d]`. -/
def srcD (d : Nat) : MemOp := { base := .rsi, index := some .r10, disp := d }
def dstD (d : Nat) : MemOp := { base := .rdi, index := some .r10, disp := d }

/-- 64 bytes from `rsi + r10` to `rdi + r10`, through `xmm0`–`xmm3`; `ZF` if
`r10` reaches `r8`. -/
def copy64Body : List Instr :=
  [.movdquLoad .xmm0 (srcD 0), .movdquLoad .xmm1 (srcD 16), .movdquLoad .xmm2 (srcD 32),
    .movdquLoad .xmm3 (srcD 48), .movdquStore (dstD 0) .xmm0, .movdquStore (dstD 16) .xmm1,
    .movdquStore (dstD 32) .xmm2, .movdquStore (dstD 48) .xmm3, .alu .add .r10 (imm 64),
    .alu .cmp .r10 (.reg .r8)]

/-- 16 bytes, through `xmm0`; `ZF` if `r10` reaches `r8`. -/
def copy16Body : List Instr :=
  [.movdquLoad .xmm0 (srcD 0), .movdquStore (dstD 0) .xmm0, .alu .add .r10 (imm 16), .alu .cmp .r10 (.reg .r8)]

/-- One byte, through `rax`; `ZF` if `r10` reaches `rcx`. -/
def copy1Body : List Instr :=
  [.movzx8 .rax (srcD 0), .store8 (dstD 0) .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)]

/-- The last 16 of the `rcx ≥ 16` bytes, through `xmm0`, from `r10 = rcx - 16`
(some of them again). -/
def copyLast : List Instr :=
  [.mov .r10 (.reg .rcx), .alu .sub .r10 (imm 16), .movdquLoad .xmm0 (srcD 0), .movdquStore (dstD 0) .xmm0]

/-- The `rcx` bytes at `rsi` copied to `rdi`: 64 at a time up to `64 ⌊rcx / 64⌋`,
16 at a time up to `16 ⌊rcx / 16⌋`, from `r10 = 0`; then the rest, if any, with
the last 16 bytes (`copyLast`, which copies again those before the rest) if
there are 16, and otherwise one at a time. -/
def copy : Prog isa :=
  .seq (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 6, .shift .shl .r8 6,
      .alu .cmp .r8 (imm 0)])
  (.seq (.ite .e (.block []) (.loop (.block copy64Body) .ne))
  (.seq (.block [.mov .r8 (.reg .rcx), .shift .shr .r8 4, .shift .shl .r8 4, .alu .cmp .r10 (.reg .r8)])
  (.seq (.ite .e (.block []) (.loop (.block copy16Body) .ne))
  (.seq (.block [.alu .cmp .r10 (.reg .rcx)])
    (.ite .e (.block [])
      (.seq (.block [.alu .cmp .rcx (imm 16)])
        (.ite .b (.loop (.block copy1Body) .ne) (.block copyLast))))))))

/-- The `r9` slices that the descriptors at `r11` list copied to `rdi`, one
after the other, as ChaCha20-Poly1305's gathering does them
(`Impl/ChaCha20Poly1305/X86_64/SealGather.lean`: `next` loads a descriptor,
`advance` moves past its slice), each with `copy`. -/
def gatherCopy : Prog isa :=
  .seq (.block [.alu .cmp .r9 (imm 0)])
    (.ite .e (.block []) (.loop (.seq (.block next) (.seq copy (.block advance))) .ne))

/-- The arguments of `vg_aes_gcm_seal(ctx, rounds, nonce, nonce_len, aad,
aad_len, dst, len, tag)`, with `tag`, `len` and `dst` in `rax`, `r10` and
`r11`, to be pushed. -/
def sealArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .rdi (.mem (at_ .r11 gCtx)), .mov .rsi (.mem (at_ .r11 gRounds)),
    .mov .rdx (.mem (at_ .r11 gState)), .mov .rcx (.mem (at_ .r11 (gState + 8))), .mov .r8 (.mem (at_ .r11 gAad)),
    .mov .r9 (.mem (at_ .r11 gAlen)), .mov .rax (.mem (at_ .r11 gTag)), .mov .r10 (.mem (at_ .r11 gLen)),
    .mov .r11 (.mem (at_ .r11 gDst))]

/-- The slices copied to the output, and encrypted there by `sealFn`
(`vg_aes_gcm_seal`), with `dst`, `len` and `tag` passed on the stack. -/
def copySeal (sealFn : Fn) : Prog isa :=
  .seq (.block copyEntry)
    (.seq gatherCopy
      (.seq (.block sealArgs) (.frame (.push [.rax, .r10, .r11]) (.call sealFn.name sealFn.code) (.pop .rax 3))))

/-! ## A short copy: the slices after the first copied, then sealed from the first -/

/-- The length of the text and of its first slice (0 if there is none) into
`r10`, with `work` in `r11`, then `last`. -/
def lenTest (last : List Instr) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (at_ .rsp 48)), .mov32 .r10 (imm 0), .mov .rax (.mem (at_ .r11 gLeft)),
      .alu .test .rax (.reg .rax)])
    (.seq (.ite .e (.block []) (.block [.mov .r10 (.mem (at_ .r11 gDesc)), .mov .r10 (.mem (at_ .r10 8))]))
      (.block last))

/-- `CF` if the text is shorter than `t` bytes, or its first slice holds all
its whole blocks (`16 ⌊len / 16⌋ ≤` its length). -/
def splitLast (t : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4, .alu .cmp .r10 (.reg .rax),
    .mov .rax (.mem (at_ .r11 gLen)), .mov32 .r10 (imm 0), .cmov .ae .rax (.reg .r10), .alu .cmp .rax (imm t)]

/-- `CF` if the text is shorter than `q` bytes, with `work` in `r11`. -/
def quickTest (q : Nat) : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .rax (.mem (at_ .r11 gLen)), .alu .cmp .rax (imm q)]

/-- `CF` if the text is shorter than `q` bytes, without reading its slices
(as the tests below are for any such text), and otherwise as `lenTest last`
sets it. -/
def lenTestQ (q : Nat) (last : List Instr) : Prog isa :=
  .seq (.block (quickTest q)) (.ite .b (.block []) (lenTest last))

/-- `CF` if the text takes the short path. -/
def splitTest (t : Nat) : Prog isa := lenTestQ t (splitLast t)

/-- `CF` unless the first slice holds all the whole blocks and at least `ts`
bytes (for `ts ≥ 1`). -/
def selLast (ts : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4, .mov32 .r8 (imm 0),
    .alu .cmp .r10 (.reg .rax), .cmov .b .r10 (.reg .r8), .alu .cmp .r10 (imm ts)]

/-- `CF` if a text on the short path is better copied whole and sealed by
`vg_aes_gcm_seal` than sealed from its first slice by `vg_aes_gcm_seal_split`
(for a text of at least `ts` bytes, which `sealGather` has already tested). -/
def selTest (ts : Nat) : Prog isa := lenTest (selLast ts)

/-- The nonce and its length kept, as `copyEntry` keeps them; `dst` in `rdi`,
the slices in `r9` and their first descriptor in `r10`, and an empty first
slice (at the descriptors) in `rax` and `rcx`; `ZF` if there is no slice. -/
def splitEntry : List Instr :=
  [.store (at_ .r11 gState) .rsi, .store (at_ .r11 (gState + 8)) .rdx, .mov .r9 (.mem (at_ .r11 gLeft)),
    .mov .rdi (.mem (at_ .r11 gDst)), .mov .r10 (.mem (at_ .r11 gDesc)), .mov .rax (.reg .r10),
    .mov32 .rcx (imm 0), .alu .test .r9 (.reg .r9)]

/-- The first slice into `rax` and `rcx`, and past it: one slice fewer, the
next descriptor, and the output after it. -/
def splitFirst : List Instr :=
  [.mov .rax (.mem (at_ .r10 0)), .mov .rcx (.mem (at_ .r10 8)), .alu .sub .r9 (imm 1), .alu .add .r10 (imm 16),
    .alu .add .rdi (.reg .rcx)]

/-- The first slice kept in the streaming state's slots after the nonce, and
the next descriptor in `r11`. -/
def splitKeep : List Instr :=
  [.store (at_ .r11 (gState + 16)) .rax, .store (at_ .r11 (gState + 24)) .rcx, .mov .r11 (.reg .r10)]

/-- The arguments of `vg_aes_gcm_seal_split(ctx, rounds, nonce, nonce_len,
aad, aad_len, src, src_len, dst, len, tag)` but `ctx` and `rounds`, with
`tag`, `len`, `dst`, `src_len` and `src` in `rax`, `r10`, `r11`, `rdi` and
`rsi`, to be pushed. -/
def splitArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .rdx (.mem (at_ .r11 gState)), .mov .rcx (.mem (at_ .r11 (gState + 8))),
    .mov .r8 (.mem (at_ .r11 gAad)), .mov .r9 (.mem (at_ .r11 gAlen)), .mov .rax (.mem (at_ .r11 gTag)),
    .mov .r10 (.mem (at_ .r11 gLen)), .mov .rdi (.mem (at_ .r11 (gState + 24))),
    .mov .rsi (.mem (at_ .r11 (gState + 16))), .mov .r11 (.mem (at_ .r11 gDst))]

/-- `ctx` and `rounds`, once the other arguments are pushed (`work` 40 bytes
further up the stack). -/
def splitCtx : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 88)), .mov .rdi (.mem (at_ .r11 gCtx)), .mov .rsi (.mem (at_ .r11 gRounds))]

/-- The slices after the first copied to the output after it, and the text
encrypted by `splitFn` (`vg_aes_gcm_seal_split`) from the first slice where
it is and the rest at the output, with `src`, `src_len`, `dst`, `len` and
`tag` passed on the stack. -/
def copySplit (splitFn : Fn) : Prog isa :=
  .seq (.seq (.block splitEntry) (.ite .e (.block []) (.block splitFirst)))
    (.seq (.block splitKeep)
      (.seq gatherCopy
        (.seq (.block splitArgs)
          (.frame (.push [.rax, .r10, .r11, .rdi, .rsi])
            (.seq (.block splitCtx) (.call splitFn.name splitFn.code)) (.pop .rax 5)))))

/-- The short path: the text copied whole and sealed by `sealFn`, or sealed
from its first slice by `splitFn`, as `selTest ts` chooses. -/
def copyShort (ts : Nat) (sealFn splitFn : Fn) : Prog isa :=
  .seq (selTest ts) (.ite .b (copySeal sealFn) (copySplit splitFn))

/-! ## A TLS record's text, before the entry -/

/-- From the entry: `CF` if the text is shorter than `t` bytes. -/
def frontLen (t : Nat) : List Instr := [.mov .rax (.mem (at_ .rsp 32)), .alu .cmp .rax (imm t)]

/-- `r11` nonzero unless the nonce is 12 bytes long, the additional data at
most 16 and there are one or two slices (`r11` starts at `nonce_len - 12`,
and each test leaves it as it was or makes it nonzero); `CF` unless there
are one or two. -/
def frontArgs : List Instr :=
  [.mov .r11 (.reg .rcx), .alu .sub .r11 (imm 12), .alu .cmp .r9 (imm 17), .cmov .ae .r11 (.reg .r9),
    .mov .rax (.mem (at_ .rsp 16)), .alu .sub .rax (imm 1), .alu .cmp .rax (imm 2), .cmov .ae .r11 (.reg .rax)]

/-- With one or two slices, `r11` made nonzero unless at most 16 bytes of
text follow the whole blocks of the first slice (of length `a`, in `r10`),
and the first slice is at least 256 bytes long if the text is (and always,
if `long`). -/
def frontSlice (long : Bool) : List Instr :=
  [.mov .r10 (.mem (at_ .rsp 8)), .mov .r10 (.mem (at_ .r10 8)),
    .mov .rax (.reg .r10), .shift .shr .rax 4, .shift .shl .rax 4, .alu .add .rax (imm 16),
    .alu .cmp .rax (.mem (at_ .rsp 32)), .cmov .ae .rax (.reg .r11), .alu .or .r11 (.reg .rax),
    .mov .rax (.mem (at_ .rsp 32))] ++ (if long then [.alu .or .rax (imm 256)] else []) ++
  [.shift .shr .rax 8, .alu .cmp .r10 (imm 256), .cmov .ae .rax (.reg .r11), .alu .or .r11 (.reg .rax)]

/-- The tests of `frontArgs` and `frontSlice long`; `ZF` if all pass. -/
def frontCore (long : Bool) : Prog isa :=
  .seq (.block frontArgs)
    (.seq (.ite .ae (.block []) (.block (frontSlice long))) (.block [.alu .test .r11 (.reg .r11)]))

/-- From the entry, with the arguments where the caller put them: `ZF` if the
text is a TLS record's (a 12-byte nonce, at most 16 bytes of additional
data, and one or two slices, the second ending at most 16 bytes after the
first's whole blocks; `frontSlice long`), which `vg_aes_gcm_seal_split`
seals fastest from its first slice. Only `rax`, `r10` and `r11` change; on
512-bit registers (`long`) a text shorter than 256 bytes leaves after the
first comparison. -/
def frontTest (long : Bool) : Prog isa :=
  if long then .seq (.block (frontLen 256)) (.ite .b (.block []) (frontCore long)) else frontCore long

/-- `ctx` and `rounds` kept in `work` (where `splitCtx` reads them), the first
descriptor in `r10`, and `ZF` if there is one slice. -/
def fastEntry : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .r10 (.mem (at_ .rsp 8)), .mov .rax (.mem (at_ .rsp 16)),
    .store (at_ .r11 gCtx) .rdi, .store (at_ .r11 gRounds) .rsi, .alu .cmp .rax (imm 1)]

/-- The second slice's length into `rcx`, `ZF` if it is empty. -/
def fastLen2 : List Instr := [.mov .rcx (.mem (at_ .r10 24)), .alu .test .rcx (.reg .rcx)]

/-- The second slice in `rsi`, the output after the first in `rdi`, and
`r10 = 0`, for a copy one byte at a time (`copy1Body`). -/
def fastCopy : List Instr :=
  [.mov .rsi (.mem (at_ .r10 16)), .mov .rdi (.mem (at_ .rsp 24)), .alu .add .rdi (.mem (at_ .r10 8)),
    .mov32 .r10 (imm 0)]

/-- The arguments of `vg_aes_gcm_seal_split(ctx, rounds, nonce, 12, aad,
aad_len, src, src_len, dst, len, tag)` but `ctx` and `rounds`, with `tag`,
`len`, `dst`, `src_len` and `src` (the first slice) in `rax`, `r10`, `r11`,
`rdi` and `rsi`, to be pushed. -/
def fastArgs : List Instr :=
  [.mov32 .rcx (imm 12), .mov .r10 (.mem (at_ .rsp 8)), .mov .rsi (.mem (at_ .r10 0)), .mov .rdi (.mem (at_ .r10 8)),
    .mov .rax (.mem (at_ .rsp 40)), .mov .r10 (.mem (at_ .rsp 32)), .mov .r11 (.mem (at_ .rsp 24))]

/-- A TLS record's text: the second slice, if any, copied to the output after
the first, and the text encrypted by `splitFn` (`vg_aes_gcm_seal_split`)
from the first slice where it is and the rest at the output, with `src`,
`src_len`, `dst`, `len` and `tag` passed on the stack. -/
def frontFast (splitFn : Fn) : Prog isa :=
  .seq (.block fastEntry)
    (.seq (.ite .e (.block [])
        (.seq (.block fastLen2) (.ite .e (.block []) (.seq (.block fastCopy) (.loop (.block copy1Body) .ne)))))
      (.seq (.block fastArgs)
        (.frame (.push [.rax, .r10, .r11, .rdi, .rsi]) (.seq (.block splitCtx) (.call splitFn.name splitFn.code))
          (.pop .rax 5))))

/-- `frontFast splitFn` if `frontTest long` sets `ZF`, and otherwise `rest`
(`sealGather`). -/
def withFront (long : Bool) (splitFn : Fn) (rest : Prog isa) : Prog isa :=
  .seq (frontTest long) (.ite .e (frontFast splitFn) rest)

/-! ## A longer text: the streaming functions -/

/-- From `vg_aes_gcm_stream_init` on: the message by the streaming functions,
and the tag. -/
def stream (init aad encTo fin : Fn) : Prog isa :=
  .seq (.call init.name init.code)
    (.seq (.block aadArgs)
      (.seq (.call aad.name aad.code)
        (.seq (text aad encTo)
          (.seq (.block finArgs) (.call fin.name fin.code)))))

/-- For a text of at least `q` bytes: `short` (`copyShort`)
if `test` (`splitTest`) sets `CF`, and otherwise `init`
(`vg_aes_gcm_stream_init`), `aad` (`vg_aes_gcm_stream_aad`), `encTo`
(`vg_aes_gcm_stream_encrypt_to`) and `fin` (`vg_aes_gcm_stream_finish`). -/
def gatherRest (test short : Prog isa) (init aad encTo fin : Fn) : Prog isa :=
  .seq test (.ite .b short (stream init aad encTo fin))

/-- `vg_aes_gcm_seal_gather`: `fast` (`copySeal`) if `quick` (the test of
the text's length alone, `quickTest q`) sets `CF`, and otherwise
`gatherRest`. -/
def sealGather (quick fast test short : Prog isa) (init aad encTo fin : Fn) : Prog isa :=
  .seq (.block entry1)
    (.seq (.block entry2)
      (.seq quick
        (.ite .b fast (gatherRest test short init aad encTo fin))))

end VG.Impl.AesGcm.X86_64.SealGather
