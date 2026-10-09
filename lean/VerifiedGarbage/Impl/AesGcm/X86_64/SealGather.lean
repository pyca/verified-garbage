import VerifiedGarbage.Impl.AesGcm.X86_64.StreamTo
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

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

A text shorter than `t` bytes (a parameter of the code, below `2^31`) is
copied, slice after slice, to the output (`copy`: 64 bytes at a time
through `xmm0`–`xmm3`, then 16, then the last 16 again, or one at a time), and encrypted there in place by
one call of `sealFn` (`vg_aes_gcm_seal` for the same implementations, with the
short path of the AVX-512 ones), with the arguments kept in `work`. The
streaming functions' calls cost more than the copy saves below `t`.

Otherwise it runs the streaming functions on a state of its own, in `work`: it starts
the message with the nonce, absorbs the additional data, and, if there is
any text, pads the additional data with zeros to a whole block (as GHASH
does), so that `vg_aes_gcm_stream_encrypt_to` encrypts the whole blocks of
each slice straight from where it is to the output; then it encrypts the
slices one after the other, each to the output after the ones before it,
and writes the tag. The arguments and the progress through the slices are
kept in `work` across the calls.
-/

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

/-- `CF` if the text is shorter than `t` bytes, and `work` in `r11`. -/
def shortTest (t : Nat) : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 48)), .mov .rax (.mem (at_ .r11 gLen)), .alu .cmp .rax (imm t)]

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

/-! ## A longer text: the streaming functions -/

/-- From `vg_aes_gcm_stream_init` on: the message by the streaming functions,
and the tag. -/
def stream (init aad encTo fin : Fn) : Prog isa :=
  .seq (.call init.name init.code)
    (.seq (.block aadArgs)
      (.seq (.call aad.name aad.code)
        (.seq (text aad encTo)
          (.seq (.block finArgs) (.call fin.name fin.code)))))

/-- `vg_aes_gcm_seal_gather`, calling `sealFn` (`vg_aes_gcm_seal`) for a text
shorter than `t` bytes, and otherwise `init` (`vg_aes_gcm_stream_init`),
`aad` (`vg_aes_gcm_stream_aad`), `encTo` (`vg_aes_gcm_stream_encrypt_to`)
and `fin` (`vg_aes_gcm_stream_finish`). -/
def sealGather (sealFn : Fn) (t : Nat) (init aad encTo fin : Fn) : Prog isa :=
  .seq (.block entry1)
    (.seq (.block entry2)
      (.seq (.block (shortTest t))
        (.ite .b (copySeal sealFn) (stream init aad encTo fin))))

end VG.Impl.AesGcm.X86_64.SealGather
