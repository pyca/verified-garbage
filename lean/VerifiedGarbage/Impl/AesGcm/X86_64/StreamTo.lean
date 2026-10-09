import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo

/-!
# AES-GCM streaming encryption, out of place: x86-64 implementation

`vg_aes_gcm_stream_encrypt_to` `(ctx = rdi, rounds = rsi, state = rdx,
aad_len = rcx, text_len = r8, src = r9, len = [rsp + 8], dst = [rsp + 16],
dst_len = [rsp + 24], work = [rsp + 32])`, its working space allocated on the
stack by `withStackArgScratch` (`work` is the argument the frame adds),
generic over the implementations of `vg_aes_gcm_encrypt_blocks_to` and
`vg_aes_gcm_stream_encrypt` it calls, as the other functions of AES-GCM.

The entry keeps the arguments in `work` (`ctx`, `rounds`, `state`, `aad_len`,
`text_len`, `src`, `len` and `dst` at `work` … `work + 56`, and the number of
bytes done, 0, at `work + 64`). If the text so far ends inside a block, the
`k` bytes that end it (or all `len`, if fewer), unless the text so far and
they would exceed 2⁶⁴ bytes, are copied from `src` to `dst` and encrypted
there by a call of `vg_aes_gcm_stream_encrypt`, and are then done (`head`,
with `k` kept at `work + 72` across the call). Then, if the text so far and
the bytes done end at the end of a block, and are not empty or follow
additional data of whole blocks (`aad_len` a multiple of 16; GHASH has then
absorbed all of its input so far, with no padding to come), the whole blocks
of what is left, if any (and if the text so far, the bytes done and they do
not exceed 2⁶⁴ bytes, so that the text so far stays exact in 64 bits), are
encrypted from `src` to `dst`, past the bytes done, and absorbed by a call of
`vg_aes_gcm_encrypt_blocks_to` on the state's counter block (`state + 48`)
and GHASH accumulator (`state + 16`), with `work + 80` for its working space
(`blocks`). What is left, if anything, is copied from `src` to `dst` and
encrypted there by a call of `vg_aes_gcm_stream_encrypt`, as the
continuation of the text so far and the bytes done (`rest`). So a slice
after one that ends inside a block is encrypted straight from where it is,
past the bytes that end that block, as one that follows a whole block is.
-/

namespace VG.Impl.AesGcm.X86_64.StreamTo

open VG.X86_64

/-- Where the entry keeps the arguments, in `work`. -/
def wCtx : Nat := 0
def wRounds : Nat := 8
def wState : Nat := 16
def wAad : Nat := 24
def wTlen : Nat := 32
def wSrc : Nat := 40
def wLen : Nat := 48
def wDst : Nat := 56
/-- The number of bytes done. -/
def wDone : Nat := 64
/-- The number of bytes of the head, across its call. -/
def wHead : Nat := 72
/-- The working space of `vg_aes_gcm_encrypt_blocks_to`. -/
def wScr : Nat := 80

/-- The arguments kept, with `work` in `r11`, and no bytes done. -/
def entry : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 32)), .mov .rax (.mem (at_ .rsp 8)), .mov .r10 (.mem (at_ .rsp 16)),
    .store (at_ .r11 wCtx) .rdi, .store (at_ .r11 wRounds) .rsi, .store (at_ .r11 wState) .rdx,
    .store (at_ .r11 wAad) .rcx, .store (at_ .r11 wTlen) .r8, .store (at_ .r11 wSrc) .r9,
    .store (at_ .r11 wLen) .rax, .store (at_ .r11 wDst) .r10, .mov32 .rax (imm 0), .store (at_ .r11 wDone) .rax]

/-- The bytes that end the block the text so far ends inside, `(-text_len)
mod 16`, or all `len` if fewer, into `rax`, and whether there are none. -/
def headLen : List Instr :=
  [.mov32 .rax (imm 0), .alu .sub .rax (.reg .r8), .alu .and .rax (imm 15), .mov .rcx (.mem (at_ .r11 wLen)),
    .alu .cmp .rcx (.reg .rax), .cmov .b .rax (.reg .rcx), .alu .test .rax (.reg .rax)]

/-- `CF` if the text so far and the `rax` bytes of the head would exceed 2⁶⁴
bytes. -/
def headOver : List Instr := [.mov .rcx (.reg .r8), .alu .add .rcx (.reg .rax)]

/-- The bytes of the head kept, and the pointers of their copy. -/
def headPtrs : List Instr :=
  [.store (at_ .r11 wHead) .rax, .mov .rcx (.reg .rax), .mov .rsi (.mem (at_ .r11 wSrc)),
    .mov .rdi (.mem (at_ .r11 wDst))]

/-- The arguments of `vg_aes_gcm_stream_encrypt` for the bytes of the head. -/
def headArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 32)), .mov .r10 (.mem (at_ .r11 wHead)), .mov .rdi (.mem (at_ .r11 wCtx)),
    .mov .rsi (.mem (at_ .r11 wRounds)), .mov .rdx (.mem (at_ .r11 wState)), .mov .rcx (.mem (at_ .r11 wAad)),
    .mov .r8 (.mem (at_ .r11 wTlen)), .mov .r9 (.mem (at_ .r11 wDst))]

/-- The bytes of the head, done. -/
def headDone : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 32)), .mov .rax (.mem (at_ .r11 wHead)), .store (at_ .r11 wDone) .rax]

/-- If the text so far ends inside a block, the bytes that end it (or all
`len`, if fewer; unless the text so far and they would exceed 2⁶⁴ bytes),
copied from `src` to `dst` (`copyLoop`) and encrypted there by `enc`
(`vg_aes_gcm_stream_encrypt`), with their number passed on the stack. -/
def head (enc : Fn) : Prog isa :=
  .seq (.block headLen)
    (.ite .e (.block [])
      (.seq (.block headOver)
        (.ite .b (.block [])
          (.seq (.block headPtrs)
            (.seq copyLoop
              (.seq (.block headArgs)
                (.seq (.frame (.push [.r10]) (.call enc.name enc.code) (.pop .rax 1)) (.block headDone))))))))

/-- `work` into `r11`, `aad_len` into `rcx`, and the text so far and the
bytes done into `r8`. -/
def blocksLoad : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 32)), .mov .rcx (.mem (at_ .r11 wAad)), .mov .r8 (.mem (at_ .r11 wTlen)),
    .mov .rax (.mem (at_ .r11 wDone)), .alu .add .r8 (.reg .rax)]

/-- The number of whole blocks left after the bytes done, into `rax`, and
whether there is none. -/
def blocksCount : List Instr :=
  [.mov .rax (.mem (at_ .r11 wLen)), .mov .rcx (.mem (at_ .r11 wDone)), .alu .sub .rax (.reg .rcx),
    .shift .shr .rax 4, .alu .test .rax (.reg .rax)]

/-- The number of whole blocks, `rax ≥ 1`, into `r9`, and their bytes into
`rax`; `CF` if the text so far, the bytes done and them would exceed 2⁶⁴
bytes. -/
def blocksLen : List Instr :=
  [.mov .r9 (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .mov .rcx (.reg .r8), .alu .add .rcx (.reg .rax)]

/-- The bytes done, with the `rax` bytes of the `r9` whole blocks, and the
arguments of `vg_aes_gcm_encrypt_blocks_to` for them, past the bytes done
before. -/
def blocksArgs : List Instr :=
  [.mov .rcx (.mem (at_ .r11 wDone)), .alu .add .rax (.reg .rcx), .store (at_ .r11 wDone) .rax,
    .mov .rdi (.mem (at_ .r11 wCtx)), .mov .rsi (.mem (at_ .r11 wRounds)), .mov .rdx (.mem (at_ .r11 wState)),
    .mov .r8 (.mem (at_ .r11 wSrc)), .alu .add .r8 (.reg .rcx), .mov .r10 (.mem (at_ .r11 wDst)),
    .alu .add .r10 (.reg .rcx), .mov .rcx (.reg .rdx), .alu .add .rcx (imm 16), .alu .add .rdx (imm 48),
    .mov .rax (.reg .r11), .alu .add .rax (imm wScr)]

/-- If the text so far and the bytes done end a block, and are not empty or
follow additional data of whole blocks (GHASH has then absorbed all of its
input so far, with no padding to come), the whole blocks left, if any (and if
the text so far, the bytes done and they do not exceed 2⁶⁴ bytes), by `blk`
(`vg_aes_gcm_encrypt_blocks_to`), with `dst`, the number of blocks and the
working space passed on the stack. -/
def blocks (blk : Fn) : Prog isa :=
  .seq (.block blocksLoad)
  (.seq (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)])
    (.seq (.ite .e (.block [.mov .rax (.reg .rcx)]) (.block []))
      (.seq (.block [.alu .and .rax (imm 15)])
        (.ite .ne (.block [])
          (.seq (.block blocksCount)
            (.ite .e (.block [])
              (.seq (.block blocksLen)
                (.ite .b (.block [])
                  (.seq (.block blocksArgs)
                    (.frame (.push [.rax, .r9, .r10]) (.call blk.name blk.code) (.pop .rax 3)))))))))))

/-- The arguments of `vg_aes_gcm_stream_encrypt` for the bytes left, after
the bytes done. -/
def restArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 32)), .mov .rax (.mem (at_ .r11 wDone)), .mov .r10 (.mem (at_ .r11 wLen)),
    .alu .sub .r10 (.reg .rax), .mov .rdi (.mem (at_ .r11 wCtx)), .mov .rsi (.mem (at_ .r11 wRounds)),
    .mov .rdx (.mem (at_ .r11 wState)), .mov .rcx (.mem (at_ .r11 wAad)), .mov .r8 (.mem (at_ .r11 wTlen)),
    .alu .add .r8 (.reg .rax), .mov .r9 (.mem (at_ .r11 wDst)), .alu .add .r9 (.reg .rax)]

/-- The bytes left, if any, copied from `src` to `dst` (`copyLoop`) and
encrypted there by `enc` (`vg_aes_gcm_stream_encrypt`), with their number
passed on the stack. -/
def rest (enc : Fn) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (at_ .rsp 32)), .mov .rcx (.mem (at_ .r11 wLen)),
      .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block [])
      (.seq (.block [.mov .rsi (.mem (at_ .r11 wSrc)), .alu .add .rsi (.reg .rax),
          .mov .rdi (.mem (at_ .r11 wDst)), .alu .add .rdi (.reg .rax)])
        (.seq copyLoop
          (.seq (.block restArgs)
            (.frame (.push [.r10]) (.call enc.name enc.code) (.pop .rax 1))))))

/-- `vg_aes_gcm_stream_encrypt_to`, calling `blk` (`vg_aes_gcm_encrypt_blocks_to`)
and `enc` (`vg_aes_gcm_stream_encrypt`). -/
def encrypt (blk enc : Fn) : Prog isa :=
  .seq (.block entry) (.seq (head enc) (.seq (blocks blk) (rest enc)))

end VG.Impl.AesGcm.X86_64.StreamTo
