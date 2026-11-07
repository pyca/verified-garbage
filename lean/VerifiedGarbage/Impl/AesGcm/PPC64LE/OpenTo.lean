module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealGather

/-!
# AES-GCM decryption out of place, by a copy: PPC64LE implementation

`vg_aes_gcm_open_to(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6,
aad = r7, aad_len = r8, src = r9, len = r10, dst, dst_len, tag, tag_len)`,
its ninth to twelfth arguments in memory (ELFv2 ABI §2.2.3.3, the Parameter
Save Area at `sp + 96`): it copies the `len` bytes at `src` to `dst`
(`Impl/Gather/PPC64LE.lean`'s `copySlice`, with `src`, `len` and `dst` in
`r3`, `r4` and `r9`), and decrypts them there in place with a call of
`vg_aes_gcm_open(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len, tag, tag_len)`,
whose `tag` and `tag_len` are its stack arguments. If it returns 0 (the tag
is wrong), `dst` holds the ciphertext again, and is zeroed a byte at a time
(`wipe`); `r3` is left as the call left it, 0.

It allocates a frame of 160 bytes. Its Parameter Save Area holds the call's
stack arguments `tag` and `tag_len` (at `sp + 96` and `sp + 104`), and the
doublewords after them (at `sp + 112`) keep `ctx`, `rounds`, `nonce` and
`nonce_len`, which the copy overwrites, and (at `sp + 152`, as
`SealGather.ret` reads it) our return address, which the call (`bl`)
overwrites in the link register. Our stack arguments `dst`, `dst_len`,
`tag` and `tag_len` are then at `sp + 256` … `sp + 280`. The copy leaves
`aad`, `aad_len` and `len` in `r7`, `r8` and `r10`. Every register the
function writes is caller-saved, and the branches are on `len` alone, but
the one after the call, on whether the tag is right.
-/

@[expose] public section

namespace VG.Impl.AesGcm.PPC64LE.OpenTo

open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-- `vg_aes_gcm_open`, in its frame. -/
def openCode : Prog isa := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesGcm.PPC64LE.open

/-- The arguments the copy overwrites, and our return address, into the
frame (`r12` its address); `tag` and `tag_len` into the call's stack
arguments; `src`, `len` and `dst` into `copySlice`'s registers. -/
def entry : List Instr :=
  [.addSp .r12 0, .store .d .r3 .r12 112, .store .d .r4 .r12 120, .store .d .r5 .r12 128,
    .store .d .r6 .r12 136, .mflr .r0, .store .d .r0 .r12 152, .load .d .r0 .r12 272, .store .d .r0 .r12 96,
    .load .d .r0 .r12 280, .store .d .r0 .r12 104, mov .r3 .r9, mov .r4 .r10, .load .d .r9 .r12 256]

/-- The call's arguments: `ctx`, `rounds`, `nonce` and `nonce_len` back from
the frame, which `r12` still points to, and `dst` from our stack arguments;
`aad`, `aad_len` and `len` are still in `r7`, `r8` and `r10`. -/
def callArgs : List Instr :=
  [.load .d .r3 .r12 112, .load .d .r4 .r12 120, .load .d .r5 .r12 128, .load .d .r6 .r12 136,
    .load .d .r9 .r12 256]

/-- `dst` in `r9`, `dst_len` (`len`) in `r10`, and zero in `r11`. -/
def wipeArgs : List Instr := [.addSp .r12 0, .load .d .r9 .r12 256, .load .d .r10 .r12 264, .li .r11 0]

/-- The `r10` bytes at `r9` zeroed, a byte at a time. -/
def wipeLoop : Prog isa :=
  .ite (.zero .d .r10) (.block [])
    (.loop (.block [.stb .r11 .r9 0, .addi .r9 .r9 1, .subi .r10 .r10 1]) (.nonzero .d .r10))

/-- The `len` bytes at `dst` zeroed. -/
def wipe : Prog isa := .seq (.block wipeArgs) wipeLoop

/-- After the call: `dst` wiped if it returned 0. -/
def after : Prog isa := .ite (.zero .w .r3) wipe (.block [])

/-- `vg_aes_gcm_open_to`, calling `vg_aes_gcm_open`. -/
def openTo : Prog isa :=
  .frame (.alloc 160)
    (.seq (.block entry)
    (.seq Gather.PPC64LE.copySlice
    (.seq (.block callArgs)
    (.seq (.call "vg_aes_gcm_open" openCode)
    (.seq after (.block SealGather.ret))))))
    (.free 160)

end VG.Impl.AesGcm.PPC64LE.OpenTo
