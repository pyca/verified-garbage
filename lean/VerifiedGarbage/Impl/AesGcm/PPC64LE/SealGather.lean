module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
public import VerifiedGarbage.Impl.Gather.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args

/-!
# AES-GCM encryption out of place, from a list of slices: PPC64LE implementation

`vg_aes_gcm_seal_gather(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6,
aad = r7, aad_len = r8, src = r9, src_count = r10, dst, len, tag)`, its
ninth to eleventh arguments in memory (ELFv2 ABI §2.2.3.3, the Parameter
Save Area at `sp + 96`): it copies the slices `src` lists, one after the
other, to `dst` (`Impl/Gather/PPC64LE.lean`, with `src`, `src_count` and
`dst` in `r7`, `r8` and `r9`), and encrypts them there in place with a call
of `vg_aes_gcm_seal(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len,
tag)`, whose `tag` is its stack argument.

It allocates a frame of 160 bytes. Its Parameter Save Area holds the call's
stack argument `tag` (at `sp + 96`), and the doublewords after it (at
`sp + 104`) keep `ctx`, `rounds`, `nonce`, `nonce_len`, `aad` and `aad_len`,
which the gathering overwrites, and our return address, which the call
(`bl`) overwrites in the link register. Our stack arguments `dst`, `len` and
`tag` are then at `sp + 256`, `sp + 264` and `sp + 272`.
-/

@[expose] public section

namespace VG.Impl.AesGcm.PPC64LE.SealGather

open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-- `vg_aes_gcm_seal`, in its frame. -/
def sealCode : Prog isa := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1 Impl.AesGcm.PPC64LE.SealFused.seal

/-- The arguments the gathering overwrites, and our return address, into the
frame (`r12` its address); `tag` into the call's stack argument; `src`,
`src_count` and `dst` into `gather`'s registers. -/
def entry : List Instr :=
  [.addSp .r12 0, .store .d .r3 .r12 104, .store .d .r4 .r12 112, .store .d .r5 .r12 120,
    .store .d .r6 .r12 128, .store .d .r7 .r12 136, .store .d .r8 .r12 144, .mflr .r0, .store .d .r0 .r12 152,
    .load .d .r0 .r12 272, .store .d .r0 .r12 96, mov .r7 .r9, mov .r8 .r10, .load .d .r9 .r12 256]

/-- The call's arguments: `ctx`, `rounds`, `nonce`, `nonce_len`, `aad` and
`aad_len` back from the frame, which `r12` still points to, and `dst` and
`len` from our stack arguments. -/
def callArgs : List Instr :=
  [.load .d .r3 .r12 104, .load .d .r4 .r12 112, .load .d .r5 .r12 120, .load .d .r6 .r12 128,
    .load .d .r7 .r12 136, .load .d .r8 .r12 144, .load .d .r9 .r12 256, .load .d .r10 .r12 264]

/-- Our return address back from the frame. -/
def ret : List Instr := [.addSp .r12 0, .load .d .r0 .r12 152, .mtlr .r0]

/-- `vg_aes_gcm_seal_gather`. -/
def sealGather : Prog isa :=
  .frame (.alloc 160)
    (.seq (.block entry)
    (.seq Gather.PPC64LE.gather
    (.seq (.block callArgs)
    (.seq (.call "vg_aes_gcm_seal" sealCode)
      (.block ret)))))
    (.free 160)

end VG.Impl.AesGcm.PPC64LE.SealGather
