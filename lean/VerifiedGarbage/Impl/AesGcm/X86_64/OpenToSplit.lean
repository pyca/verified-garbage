module

public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenTo
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# AES-GCM decryption out of place, in one pass: x86-64 implementation

`vg_aes_gcm_open_to`, whatever the length, by a call of an instance of
`vg_aes_gcm_open_split` (`f`), which decrypts the ciphertext at `src` to
`dst` as it absorbs it, with no copy.

`openToSplit f` takes `open_to`'s arguments and a working space of 2560 bytes
after them, `work = [rsp + 56]`, which `withStackArgScratch` allocates on the
stack. Its frame is `open_to`'s, of eleven words, so that its stack arguments
are at `rsp + 96` … `rsp + 144`; it stores the call's seven stack arguments
in the frame's lowest seven words (`dst`, `len`, `tag`, `tag_len`, `src`,
`len` again for `src_len`, and `work`), with the stack pointer a multiple of
16 at the call, and calls
`f(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len, tag, tag_len, src, len, work)`,
whose six register arguments are still ours. If it returns 0 (the tag is
wrong), `dst` is zeroed (`OpenTo.after`).
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.OpenToSplit

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm Fn)
open VG.Impl.AesGcm.X86_64.OpenTo (frameRegs stArg after)

/-- The call's seven stack arguments, into the lowest seven words of our
frame. -/
def callArgs : Prog isa :=
  .seq (.block (stArg 0 112)) (.seq (.block (stArg 8 104)) (.seq (.block (stArg 16 128))
    (.seq (.block (stArg 24 136)) (.seq (.block (stArg 32 96)) (.seq (.block (stArg 40 104))
      (.block (stArg 48 144)))))))

/-- `vg_aes_gcm_open_to` with its working space as an argument, calling the
instance `f` of `vg_aes_gcm_open_split`. -/
def openToSplit (f : Fn) : Prog isa :=
  .frame (.push frameRegs) (.seq callArgs (.seq (.call f.name f.code) after)) (.pop .r11 11)

/-- The frame `withStackArgScratch` allocates for `openToSplit`: a word for the
return address, a copy of the six stack arguments, the address of the
working space and its 2560 bytes. -/
abbrev scratchBytes : Nat := 2624

end VG.Impl.AesGcm.X86_64.OpenToSplit
