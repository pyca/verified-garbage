import VerifiedGarbage.Impl.AesGcm.Arm

/-!
# AES-GCM one-shot encryption out of place, from a list of slices: 32-bit ARM implementation

`vg_aes_gcm_seal_gather(ctx = r0, rounds = r1, nonce = r2, nonce_len = r3,
aad = [sp], aad_len = [sp + 4], src = [sp + 8], src_count = [sp + 12],
dst = [sp + 16], len = [sp + 20], tag = [sp + 24])` copies the slices `src`
lists, one after the other, to `dst`, and encrypts them there in place with
a call of `vg_aes_gcm_seal(ctx, rounds, nonce, nonce_len, aad, aad_len, dst,
len, tag)` (`seal`, its symbol and code).

It allocates a frame of 40 bytes: the call's five stack arguments at `sp`
… `sp + 16`, our return address, which the call (`bl`) overwrites in `lr`,
at `sp + 20`, and `r0`–`r3`, which the copy uses, at `sp + 24` … `sp + 36`;
our stack arguments are then at `sp + 40` … `sp + 64`. The copy has `r0` at
the next descriptor, `r1` the number of slices left and `r2` where the next
slice goes; each slice is copied a word at a time through `lr`, with `r3`
its address and `r12` its number of words (`copyWords`), then its last
`len mod 4` bytes one at a time (`copyBytes`). Every register the function
writes is caller-saved, and the branches are on `src_count` and the slices'
lengths alone.
-/

namespace VG.Impl.AesGcm.Arm.SealGather

open VG.Arm

/-- `r12` at the frame; our return address and `r0`–`r3` kept in it; the
call's stack arguments `aad`, `aad_len`, `dst`, `len` and `tag` laid out in
it; and the copy's registers: `src`, `src_count` and `dst`. -/
def entry : List Instr :=
  [.addSp .r12 0, .str .lr .r12 20, .str .r0 .r12 24, .str .r1 .r12 28, .str .r2 .r12 32,
    .str .r3 .r12 36,
    .ldrSp .lr 40, .str .lr .r12 0, .ldrSp .lr 44, .str .lr .r12 4, .ldrSp .lr 56, .str .lr .r12 8,
    .ldrSp .lr 60, .str .lr .r12 12, .ldrSp .lr 64, .str .lr .r12 16,
    .ldrSp .r0 48, .ldrSp .r1 52, .ldrSp .r2 56]

/-- Copies the `r12` (at least 1) words at `r3` to `r2`, through `lr`. -/
def copyWordsLoop : Prog isa :=
  .loop (.block [.ldr .lr .r3 0, .str .lr .r2 0, addI .r3 .r3 4, addI .r2 .r2 4,
    .subs .r12 .r12 (imm 1)]) .ne

/-- Copies the `r12` (at least 1) bytes at `r3` to `r2`, through `lr`. -/
def copyBytesLoop : Prog isa :=
  .loop (.block [.ldrb .lr .r3 0, .strb .lr .r2 0, addI .r3 .r3 1, addI .r2 .r2 1,
    .subs .r12 .r12 (imm 1)]) .ne

/-- Copies the slice that the descriptor at `r0` lists to `r2`, advancing
`r2` past it: its whole words, then its last bytes, whose number is the
length (reloaded from the descriptor) modulo 4. -/
def copySlice : Prog isa :=
  .seq (.block [.ldr .r3 .r0 0, .ldr .r12 .r0 4, .mov .r12 (.shifted .r12 .lsr 2), .cmp .r12 (imm 0)])
  (.seq (.ite .eq (.block []) copyWordsLoop)
  (.seq (.block [.ldr .r12 .r0 4, .dp .and .r12 .r12 (imm 3), .cmp .r12 (imm 0)])
    (.ite .eq (.block []) copyBytesLoop)))

/-- Copies the `r1` (at least 1) slices that the descriptors at `r0` list to
`r2`, one after the other. -/
def gatherLoop : Prog isa :=
  .loop (.seq copySlice (.block [addI .r0 .r0 8, .subs .r1 .r1 (imm 1)])) .ne

/-- Copies the `r1` slices that the descriptors at `r0` list to `r2`. -/
def gather : Prog isa := .seq (.block [.cmp .r1 (imm 0)]) (.ite .eq (.block []) gatherLoop)

/-- `r0`–`r3` back from the frame. -/
def callArgs : List Instr := [.ldrSp .r0 24, .ldrSp .r1 28, .ldrSp .r2 32, .ldrSp .r3 36]

/-- `vg_aes_gcm_seal_gather`, calling `vg_aes_gcm_seal` (`name`, `code`). -/
def sealGather (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc 40)
    (.seq (.block entry)
    (.seq gather
    (.seq (.block callArgs)
    (.seq (.call name code)
      (.block [.ldrSp .lr 20])))))
    (.free 40)

end VG.Impl.AesGcm.Arm.SealGather
