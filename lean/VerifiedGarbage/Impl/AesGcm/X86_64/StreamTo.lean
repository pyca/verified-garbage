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
bytes done, 0, at `work + 64`). If the text so far is not empty and ends at
the end of a block (`text_len` a multiple of 16, not 0), the `16 ⌊len / 16⌋`
bytes of whole blocks, if any (and if `text_len` and they do not exceed 2⁶⁴
bytes, so that the text so far stays exact in 64 bits), are encrypted from `src` to `dst` and absorbed
by a call of `vg_aes_gcm_encrypt_blocks_to` on the state's counter block
(`state + 48`) and GHASH accumulator (`state + 16`), with `work + 80` for its
working space (`blocks`). What is left, if anything, is copied from `src` to
`dst` and encrypted there by a call of `vg_aes_gcm_stream_encrypt`, as the
continuation of the text so far and the blocks (`rest`).
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
/-- The working space of `vg_aes_gcm_encrypt_blocks_to`. -/
def wScr : Nat := 80

/-- The arguments kept, with `work` in `r11`, and no bytes done. -/
def entry : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 32)), .mov .rax (.mem (at_ .rsp 8)), .mov .r10 (.mem (at_ .rsp 16)),
    .store (at_ .r11 wCtx) .rdi, .store (at_ .r11 wRounds) .rsi, .store (at_ .r11 wState) .rdx,
    .store (at_ .r11 wAad) .rcx, .store (at_ .r11 wTlen) .r8, .store (at_ .r11 wSrc) .r9,
    .store (at_ .r11 wLen) .rax, .store (at_ .r11 wDst) .r10, .mov32 .rax (imm 0), .store (at_ .r11 wDone) .rax]

/-- The number of whole blocks, `rax ≥ 1`, into `r9`, and their bytes into
`rax`; `CF` if the text so far and them would exceed 2⁶⁴ bytes. -/
def blocksLen : List Instr :=
  [.mov .r9 (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .mov .rcx (.reg .r8), .alu .add .rcx (.reg .rax)]

/-- The arguments of `vg_aes_gcm_encrypt_blocks_to` for the `r9` whole
blocks, and the bytes done, their `rax` bytes. -/
def blocksArgs : List Instr :=
  [.store (at_ .r11 wDone) .rax, .mov .rdi (.mem (at_ .r11 wCtx)),
    .mov .rsi (.mem (at_ .r11 wRounds)), .mov .rdx (.mem (at_ .r11 wState)), .mov .rcx (.reg .rdx),
    .alu .add .rcx (imm 16), .alu .add .rdx (imm 48), .mov .r8 (.mem (at_ .r11 wSrc)),
    .mov .r10 (.mem (at_ .r11 wDst)), .mov .rax (.reg .r11), .alu .add .rax (imm wScr)]

/-- If the text so far is not empty and ends a block, the whole blocks, if
any (and if the text so far and they do not exceed 2⁶⁴ bytes), by `blk`
(`vg_aes_gcm_encrypt_blocks_to`), with `dst`, the number of blocks and the
working space passed on the stack. -/
def blocks (blk : Fn) : Prog isa :=
  .seq (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)])
    (.ite .e (.block [])
      (.seq (.block [.alu .and .rax (imm 15)])
        (.ite .ne (.block [])
          (.seq (.block [.mov .rax (.mem (at_ .r11 wLen)), .shift .shr .rax 4, .alu .test .rax (.reg .rax)])
            (.ite .e (.block [])
              (.seq (.block blocksLen)
                (.ite .b (.block [])
                  (.seq (.block blocksArgs)
                    (.frame (.push [.rax, .r9, .r10]) (.call blk.name blk.code) (.pop .rax 3))))))))))

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
  .seq (.block entry) (.seq (blocks blk) (rest enc))

end VG.Impl.AesGcm.X86_64.StreamTo
