module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealGather

/-!
# AES-GCM decryption out of place, in one pass: PPC64LE implementation

`vg_aes_gcm_open_to(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6,
aad = r7, aad_len = r8, src = r9, len = r10, dst, dst_len, tag, tag_len)`,
its ninth to twelfth arguments in memory (ELFv2 ABI §2.2.3.3, the Parameter
Save Area at `sp + 96`), calls `vg_aes_gcm_open_split`, which is `open`'s
body (`openWith`) with a decryption from `src` to `dst` in place of
`oneCrypt`: it hashes the ciphertext at `src` and, if the tag is right,
decrypts it straight to `dst`, with no copy.

## `vg_aes_gcm_open_split`

`(ctx, rounds, nonce, nonce_len, aad, aad_len, src = r9, len = r10,
tag = [sp + 96], tag_len = [sp + 104], scratch = [sp + 112],
dst = [sp + 120])`: `open`'s arguments, the data being the source, with the
destination after them. `oneCryptTo` decrypts the `len` bytes at `src`
(`r24`) to `dst` (`r26`, loaded from the stack): the whole blocks by
`vg_aes_ctr32_to`, from the source to the destination (`wholeTo`), then
the last bytes by `open`'s own tail, `cryptTailWith`, writing to the
destination. Nothing is copied. If the tag is wrong, `dst` is left as it was.

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

def ctrToCall : Prog isa := .call "vg_aes_ctr32_to" Impl.Aes.PPC64LE.ctr32To

/-- `splitCtr` from the source `r24`, with the destination `r26` kept in
`r10` and advanced past the whole blocks. -/
def splitTo : List Instr := splitCtr ++ [mov .r10 .r26, .add .r26 .r26 .r9]

/-- The arguments of `vg_aes_ctr32_to` but the source and the number of
blocks: the key schedule, the rounds, the counter block and the
destination. -/
def toArgs : List Instr := [mov .r3 .r29, mov .r4 .r28, .addi .r5 .r30 48, mov .r8 .r10]

/-- The whole blocks at `r24`, decrypted to `r26`. -/
def wholeTo : Prog isa := wholeWith splitTo toArgs ctrToCall

/-- The `r25` bytes at `r24` decrypted to `r26`, from the first counter block:
the whole blocks, then the last bytes. -/
def cryptTo : Prog isa :=
  .ite (.zero .d .r25) (.block []) (.seq wholeTo (cryptTailWith true))

/-- The data, its length and the destination (`[sp + 120]`). -/
def dataTo : List Instr := [mov .r24 .r27, mov .r25 .r23, .addSp .r12 0, .load .d .r26 .r12 120]

/-- The data decrypted to the destination. -/
def oneCryptTo : Prog isa := .seq (.block dataTo) cryptTo

/-- `vg_aes_gcm_open_split`. -/
def openSplit : Prog isa := openWith oneCryptTo

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
