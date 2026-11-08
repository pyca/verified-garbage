module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealGather
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SplitBlocks

/-!
# AES-GCM decryption out of place, in one pass: PPC64LE implementation

`vg_aes_gcm_open_to(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6,
aad = r7, aad_len = r8, src = r9, len = r10, dst, dst_len, tag, tag_len)`,
its ninth to twelfth arguments in memory (ELFv2 ABI §2.2.3.3, the Parameter
Save Area at `sp + 96`), calls `vg_aes_gcm_open_split`, which hashes the ciphertext at `src` and
decrypts it straight to `dst` in the same pass, with no copy.

## `vg_aes_gcm_open_split`

`(ctx, rounds, nonce, nonce_len, aad, aad_len, src = r9, len = r10,
tag = [sp + 96], tag_len = [sp + 104], scratch = [sp + 112],
dst = [sp + 120])`: `open`'s arguments, the data being the source, with the
destination after them. After the additional data, and the received tag
copied to the working space, `passData` decrypts the whole blocks from
`src` to `dst` and hashes them, in one pass, by
`vg_aes_gcm_decrypt_blocks_to`, then the last bytes by `open`'s own tail,
`cryptTailWith`, writing to the destination, and hashes those. The tags are
compared last: if they differ, `dst` holds the decryption all the same, and
the caller, `vg_aes_gcm_open_to`, wipes it.

## `vg_aes_gcm_open_to`

It allocates a frame of 2720 bytes: its Parameter Save Area holds the call's
stack arguments `tag`, `tag_len`, the address of the working space (at
`sp + 160`) and `dst` (at `sp + 96` … `sp + 120`), and our return address
(at `sp + 152`, as `SealGather.ret` reads it), which the call (`bl`)
overwrites in the link register; the working space, 2560 bytes, follows.
Our stack arguments `dst`, `dst_len`, `tag` and `tag_len` are at
`sp + 2816` … `sp + 2840`, and our register arguments are the call's. If
the call returns 0 (the tag is wrong), `dst` is zeroed a byte at a time
(`wipe`); `r3` is left as the call left it, 0. Every register the function
writes is caller-saved, and the branches are on `len` alone, but the one
after the call, on whether the tag is right.
-/

@[expose] public section

namespace VG.Impl.AesGcm.PPC64LE.OpenTo

open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-! ## `vg_aes_gcm_open_split` -/

/-- The destination (`[sp + 120]`) into `r26`, which the call keeps, and the
arguments of `vg_aes_gcm_decrypt_blocks_to` on the whole blocks of the data:
the key schedule, the rounds, the state from its accumulator (at `r30 + 16`,
the counter block 32 bytes after it), the source and their number, the
destination and their number again, and the working space. -/
def wholeArgs : List Instr :=
  [.addSp .r12 0, .load .d .r26 .r12 120, mov .r3 .r29, mov .r4 .r28, .addi .r5 .r30 16, mov .r6 .r27,
   .lsr .d .r7 .r23 4, mov .r8 .r26, mov .r9 .r7, .addi .r10 .r31 448]

/-- The whole blocks decrypted from the source to the destination, and hashed. -/
def whole : Prog isa :=
  .seq (.block wholeArgs) (.call "vg_aes_gcm_decrypt_blocks_to" Impl.AesGcm.PPC64LE.SplitBlocks.decryptTo)

/-- The last `len mod 16` bytes: their number in `r25`, their address in the
source in `r24` and in the destination in `r26` (from the destination in it). -/
def partArgs : List Instr :=
  [.li .r0 15, .logic .and .r25 .r23 .r0, .sub .r12 .r23 .r25, .add .r24 .r27 .r12, .add .r26 .r26 .r12]

/-- The data decrypted to the destination and hashed, in one pass: the whole
blocks, then the last bytes decrypted (`cryptTailWith`) and, with seal's
arguments for them (`SealFused.tailSetup`), buffered for GHASH (`absorb`). -/
def passData : Prog isa :=
  .seq whole
  (.seq (.seq (.block partArgs) (cryptTailWith true))
  (.seq (.block SealFused.tailSetup) (absorb 16)))

/-- `open` once the tag length is allowed, in one pass: the nonce's length
back in `r25`, the additional data hashed, the received tag copied to `W`
(before the destination, which may be where it is, is written), the data
decrypted to the destination while its tag is computed into `W + 112`, and
the two compared (`r3`). -/
def openPass : Prog isa :=
  .seq (.block [mov .r25 .r18])
  (.seq oneAad
  (.seq recv
  (.seq (.ite (.zero .d .r23) (oneTag 112) (.seq passData (finTag 112)))
    (cmp 112))))

/-- `vg_aes_gcm_open_split`. -/
def openSplit : Prog isa :=
  .seq (.block openEntry)
  (.seq tagLenOk
  (.seq (.ite (.zero .d .r25) (.block [.li .r3 0]) openPass)
    (.block restore)))

/-! ## `vg_aes_gcm_open_to` -/

/-- Our return address into the frame (`r12` its address); `tag`,
`tag_len`, the working space and `dst` into the call's stack arguments. -/
def entry : List Instr :=
  [.addSp .r12 0, .mflr .r0, .store .d .r0 .r12 152, .load .d .r0 .r12 2832, .store .d .r0 .r12 96,
    .load .d .r0 .r12 2840, .store .d .r0 .r12 104, .addi .r0 .r12 160, .store .d .r0 .r12 112,
    .load .d .r0 .r12 2816, .store .d .r0 .r12 120]

/-- `dst` in `r9`, `dst_len` (`len`) in `r10`, and zero in `r11`. -/
def wipeArgs : List Instr := [.addSp .r12 0, .load .d .r9 .r12 2816, .load .d .r10 .r12 2824, .li .r11 0]

/-- The `r10` bytes at `r9` zeroed, a byte at a time. -/
def wipeLoop : Prog isa :=
  .ite (.zero .d .r10) (.block [])
    (.loop (.block [.stb .r11 .r9 0, .addi .r9 .r9 1, .subi .r10 .r10 1]) (.nonzero .d .r10))

/-- The `len` bytes at `dst` zeroed. -/
def wipe : Prog isa := .seq (.block wipeArgs) wipeLoop

/-- After the call: `dst` wiped if it returned 0. -/
def after : Prog isa := .ite (.zero .w .r3) wipe (.block [])

/-- `vg_aes_gcm_open_to`, calling `vg_aes_gcm_open_split`. -/
def openTo : Prog isa :=
  .frame (.alloc 2720)
    (.seq (.block entry)
    (.seq (.call "vg_aes_gcm_open_split" openSplit)
    (.seq after (.block SealGather.ret))))
    (.free 2720)

end VG.Impl.AesGcm.PPC64LE.OpenTo
