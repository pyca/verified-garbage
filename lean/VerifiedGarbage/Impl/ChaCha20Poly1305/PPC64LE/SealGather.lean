module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.PPC64LE
public import VerifiedGarbage.Impl.Gather.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices: PPC64LE implementation

`vg_chacha20_poly1305_seal_gather(key = r3, nonce = r4, aad = r5,
aad_len = r6, src = r7, src_count = r8, dst = r9, len = r10, tag)`, its
ninth argument `tag` in memory (ELFv2 ABI §2.2.3.3, the Parameter Save Area
at `sp + 96`): it copies the slices `src` lists, one after the other, to
`dst` (`Impl/Gather/PPC64LE.lean`, whose registers `src`, `src_count` and
`dst` already are), and encrypts them there in place with a call of
`vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, dst, len, tag)`.

It allocates a frame of 80 bytes, whose local variable space (at `sp + 32`)
keeps `key`, `nonce`, `aad`, `aad_len` and `dst`, which the gathering
overwrites, and our return address, which the call (`bl`) overwrites in the
link register; our stack argument `tag` is then at `sp + 176`. `len` and
`tag` wait for the call in `r10` and `r11`, which the gathering does not
write.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.PPC64LE.SealGather

open VG.PPC64LE
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)

/-- `vg_chacha20_poly1305_seal`, in its frame. -/
def sealCode : Prog isa :=
  Impl.StackScratch.PPC64LE.withStackScratchWiped 688 .r10 81 Impl.ChaCha20Poly1305.PPC64LE.«seal»

/-- The arguments the gathering overwrites, and our return address, into the
frame (`r12` its address); `tag` into `r11`. -/
def entry : List Instr :=
  [.addSp .r12 0, .store .d .r3 .r12 32, .store .d .r4 .r12 40, .store .d .r5 .r12 48,
    .store .d .r6 .r12 56, .store .d .r9 .r12 64, .mflr .r0, .store .d .r0 .r12 72,
    .load .d .r11 .r12 176]

/-- The call's arguments: `key`, `nonce`, `aad`, `aad_len` and `dst` back
from the frame, which `r12` still points to, and `len` and `tag`. -/
def callArgs : List Instr :=
  [.load .d .r3 .r12 32, .load .d .r4 .r12 40, .load .d .r5 .r12 48, .load .d .r6 .r12 56,
    .load .d .r7 .r12 64, mov .r8 .r10, mov .r9 .r11]

/-- Our return address back from the frame. -/
def ret : List Instr := [.addSp .r12 0, .load .d .r0 .r12 72, .mtlr .r0]

/-- `vg_chacha20_poly1305_seal_gather`. -/
def sealGather : Prog isa :=
  .frame (.alloc 80)
    (.seq (.block entry)
    (.seq Gather.PPC64LE.gather
    (.seq (.block callArgs)
    (.seq (.call "vg_chacha20_poly1305_seal" sealCode)
      (.block ret)))))
    (.free 80)

end VG.Impl.ChaCha20Poly1305.PPC64LE.SealGather
