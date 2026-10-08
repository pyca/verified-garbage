import VerifiedGarbage.Impl.AesGcm.X86_64.Blocks

/-!
# AES-GCM on whole blocks, out of place: x86-64 implementation

`vg_aes_gcm_encrypt_blocks_to` `(ctx = rdi, rounds = rsi, counter = rdx,
y = rcx, src = r8, n = r9, dst = [rsp + 8], dst_n = [rsp + 16],
scratch = [rsp + 24])`, generic over the implementations of
`vg_aes_gcm_encrypt_blocks` it calls, as the other functions of AES-GCM.

The entry keeps the arguments in `scratch` (`ctx`, `rounds`, `counter`, `y`,
`src`, `n` and `dst` at `scratch` … `scratch + 48`). With a `piece` (loops
that interleave counter mode and GHASH out of place, `Gcm.X86_64.Stitch.SPreTo`,
entered with `dst` in `r10`), the first `16 ⌊n / 16⌋` blocks, if any, are
encrypted from `src` to `dst` and hashed in one pass by it (with
`scratch + 64` for its working space), and the arguments kept become those
of the rest. The rest (all the blocks, without a `piece`) is copied from
`src` to `dst` (`copyBlocks`), and encrypted and hashed there in place by a
call of `vg_aes_gcm_encrypt_blocks`, given `scratch` for its working space.
-/

namespace VG.Impl.AesGcm.X86_64.BlocksTo

open VG.X86_64
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)

/-- Where the entry keeps `src` and `dst`, in `scratch` (`Blocks.argData`
holds `src`). -/
def argSrc : Nat := 32
def argDst : Nat := 48

/-- The arguments kept, with `scratch` in `r11` and `dst` in `r10`. -/
def entry : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 24)), .mov .r10 (.mem (at_ .rsp 8)), .store (at_ .r11 argCtx) .rdi,
    .store (at_ .r11 argRounds) .rsi, .store (at_ .r11 argCtr) .rdx, .store (at_ .r11 argY) .rcx,
    .store (at_ .r11 argSrc) .r8, .store (at_ .r11 argN) .r9, .store (at_ .r11 argDst) .r10]

/-- If there are at least 16 blocks, the first `16 ⌊n / 16⌋` by `piece`,
with `dst` still in `r10` and `r11` at its working space, `scratch + 64`,
rounded up to 64 bytes when `aligned`. -/
def stitchPart (piece : Prog isa) (aligned : Bool := false) : Prog isa :=
  .seq (.block [.alu .cmp .r9 (imm 16)])
    (.ite .b (.block [])
      (.seq (.block ([.mov .rax (.reg .r9), .alu .and .rax (imm 15), .alu .sub .r9 (.reg .rax)] ++
        Blocks.scratchSetup aligned)) piece))

/-- The arguments of the rest: `n mod 16` blocks after the first
`16 ⌊n / 16⌋`, at `src` and `dst` advanced past them. -/
def rest : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 24)), .mov .r8 (.mem (at_ .r11 argN)), .mov .rax (.reg .r8),
    .alu .and .r8 (imm 15), .alu .sub .rax (.reg .r8), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .mov .rcx (.reg .rax),
    .alu .add .rax (.mem (at_ .r11 argSrc)), .store (at_ .r11 argSrc) .rax,
    .alu .add .rcx (.mem (at_ .r11 argDst)), .store (at_ .r11 argDst) .rcx, .store (at_ .r11 argN) .r8]

/-- Copies the `rcx` (at least 1) blocks at `rsi` to `rdi`, one at a time
through `xmm0`. -/
def copyBlocks : Prog isa :=
  .seq (.block [.mov32 .r10 (imm 0)])
    (.loop (.block [.movdquLoad .xmm0 srcB, .movdquStore dstB .xmm0, .alu .add .r10 (imm 16),
      .alu .sub .rcx (imm 1)]) .ne)

/-- The `n` blocks kept copied from `src` to `dst`, then encrypted and hashed
there by a call of `enc` (`vg_aes_gcm_encrypt_blocks`), with `scratch`
passed on the stack; nothing if `n` is 0. -/
def tail (enc : Fn) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rcx (.mem (at_ .r11 argN)), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block [])
      (.seq (.block [.mov .rsi (.mem (at_ .r11 argSrc)), .mov .rdi (.mem (at_ .r11 argDst))])
      (.seq copyBlocks
      (.seq (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rdi (.mem (at_ .r11 argCtx)),
          .mov .rsi (.mem (at_ .r11 argRounds)), .mov .rdx (.mem (at_ .r11 argCtr)),
          .mov .rcx (.mem (at_ .r11 argY)), .mov .r8 (.mem (at_ .r11 argDst)), .mov .r9 (.mem (at_ .r11 argN)),
          .mov .rax (.reg .r11)])
        (.frame (.push [.rax]) (.call enc.name enc.code) (.pop .rax 1))))))

/-- The first blocks by `piece`, if any, then the rest. -/
def head (piece : Option (Prog isa)) (aligned : Bool := false) : Prog isa :=
  match piece with
  | some piece => .seq (stitchPart piece aligned) (.block rest)
  | none => .block []

/-- `vg_aes_gcm_encrypt_blocks_to`, with the out-of-place encrypting `piece`,
if any, and calling `enc` (`vg_aes_gcm_encrypt_blocks`) for the rest. -/
def encrypt (enc : Fn) (piece : Option (Prog isa)) (aligned : Bool := false) : Prog isa :=
  .seq (.block entry) (.seq (head piece aligned) (tail enc))

end VG.Impl.AesGcm.X86_64.BlocksTo
