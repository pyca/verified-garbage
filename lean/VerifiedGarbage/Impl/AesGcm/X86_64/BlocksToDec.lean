module

public import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo

/-!
# AES-GCM decryption of whole blocks, out of place: x86-64 implementation

`vg_aes_gcm_decrypt_blocks_to` `(ctx = rdi, rounds = rsi, counter = rdx,
y = rcx, src = r8, n = r9, dst = [rsp + 8], dst_n = [rsp + 16],
scratch = [rsp + 24])`: `vg_aes_gcm_encrypt_blocks_to`'s code
(`BlocksTo.encrypt`), with a `piece` that decrypts out of place
(`Gcm.X86_64.Stitch.DPostTo`, the first `16 ⌊n / 16⌋` blocks, if any), and
calling `vg_aes_gcm_decrypt_blocks` (`dec`) in place for the rest, which it
copies from `src` to `dst` first: GHASH absorbs the ciphertext, which the
piece reads from `src` and the call from its copy.

`decryptTo gh ctrTo`, for the implementations with no such loop, takes the
same arguments and copies nothing: after the entry, the `n` blocks at `src`
are hashed by a call of `vg_ghash` (`gh`), then decrypted from `src` to
`dst` by a call of `vg_aes_ctr32_to` (`ctrTo`), `vg_aes_ctr32` out of place,
both with `scratch + 64` for their working space and the arguments reloaded
from `scratch` for each call, as `vg_aes_gcm_decrypt_blocks` hashes and then
decrypts in place.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.BlocksToDec

open VG.X86_64
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Impl.AesGcm.X86_64.BlocksTo (argSrc argDst)

/-- `vg_aes_gcm_decrypt_blocks_to`, with the out-of-place decrypting
`piece`, if any, and calling `dec` (`vg_aes_gcm_decrypt_blocks`) for the
rest. -/
def decrypt (dec : Fn) (piece : Option (Prog isa)) (aligned : Bool := false) : Prog isa :=
  BlocksTo.encrypt dec piece aligned false

/-- The arguments of `vg_ghash` on the blocks at `src`. -/
def ghArgsAt (dataSlot : Nat) (compact : Bool := false) : List Instr :=
  [.mov .r11 (.mem (at_ .rsp (if compact then 8 else 24))), .mov .rdi (.mem (at_ .r11 argCtx)), .alu .add .rdi (imm 240),
    .mov .rsi (.mem (at_ .r11 argY)), .mov .rdx (.mem (at_ .r11 dataSlot)), .mov .rcx (.mem (at_ .r11 argN)),
    .mov .r8 (.reg .r11), .alu .add .r8 (imm 64)]

abbrev ghArgsTo : List Instr := ghArgsAt argSrc

/-- The arguments of `vg_aes_ctr32_to` on them, from `src` to `dst` (in
`r11`, loaded last). -/
def ctrArgsTo (compact : Bool := false) : List Instr :=
  [.mov .r11 (.mem (at_ .rsp (if compact then 8 else 24))), .mov .rdi (.mem (at_ .r11 argCtx)), .mov .rsi (.mem (at_ .r11 argRounds)),
    .mov .rdx (.mem (at_ .r11 argCtr)), .mov .rcx (.mem (at_ .r11 argSrc)), .mov .r8 (.mem (at_ .r11 argN)),
    .mov .r9 (.reg .r11), .alu .add .r9 (imm 64), .mov .r11 (.mem (at_ .r11 argDst))]

/-- The `n` blocks, if any, hashed at `src` by `gh` (`vg_ghash`) and then
decrypted from `src` to `dst` by `ctrTo` (`vg_aes_ctr32_to`). -/
def tailTo (gh ctrTo : Fn) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rcx (.mem (at_ .r11 argN)), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block [])
      (.seq (.seq (.block ghArgsTo) (.call gh.name gh.code)) (.seq (.block ctrArgsTo) (.call ctrTo.name ctrTo.code))))

/-- `vg_aes_gcm_decrypt_blocks_to` with no out-of-place loop, calling `gh`
(`vg_ghash`) and `ctrTo` (`vg_aes_ctr32_to`), and copying nothing. -/
def decryptTo (gh ctrTo : Fn) : Prog isa :=
  .seq (.block BlocksTo.entry) (tailTo gh ctrTo)

/-- On a short encryption the existing out-of-place counter routine writes
the ciphertext, then GHASH consumes it at its destination. -/
def encryptShort (ctrTo gh : Fn) (compact : Bool := false) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (at_ .rsp (if compact then 8 else 24))), .mov .rcx (.mem (at_ .r11 argN)), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block [])
      (.seq (.seq (.block (ctrArgsTo compact)) (.call ctrTo.name ctrTo.code))
        (.seq (.block (ghArgsAt argDst compact)) (.call gh.name gh.code))))

/-- Prepared encryption with a fused loop for messages of at least sixteen
blocks. Both branches start with the same saved arguments. -/
def encryptPrepared (ctrTo gh : Fn) (piece : Prog isa) (aligned : Bool) (minimum : Nat := 16) : Prog isa :=
  .seq (.block BlocksTo.entry) (.seq (BlocksTo.stitchPart piece aligned true minimum) (encryptShort ctrTo gh))

/-- Internal whole-block seal entry. The destination is in r10 for both
layouts and the only stack argument is scratch. A fused loop that consumes
the whole record returns without spilling the cursors or entering the tail. -/
def sealPrepared (ctrTo gh : Fn) (piece : Prog isa) (aligned : Bool) (minimum : Nat) : Prog isa :=
  .seq (BlocksTo.compareCount minimum)
    (.ite .b (.seq (.block (BlocksTo.entry true)) (encryptShort ctrTo gh true))
      (.seq (.block (BlocksTo.pointers true ++ Blocks.scratchSetup aligned)) piece))

end VG.Impl.AesGcm.X86_64.BlocksToDec
