module

public import VerifiedGarbage.Impl.Aes.X86.AesNi
public import VerifiedGarbage.Impl.Aes.X86.ExpandKey
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# AES's key expansion on x86 (32-bit), as emitted

`vg_aes_expand_key` (`Impl.Aes.X86.expandKey`) and
`vg_aes_expand_key_aesni` (`Impl.Aes.X86.AesNi.expandKey`), each in a frame
of 532 bytes of its own whose first 128 words it zeroes before it returns
(`withStackScratchWiped`), then its cleanup (`Impl.Scrub.X86.scrubF 0 532`):
those 532 bytes of stack below `esp` zeroed, and the registers a callee may
change cleared, so that it returns without secret residue.
-/

-- separate module: a definition in `ExpandKey.lean` or `AesNi.lean` rebuilds every AES caller on x86

@[expose] public section

namespace VG.Impl.Aes.X86.Fn

open VG.X86
open Impl.StackScratch.X86 (withStackScratchWiped)

/-- `vg_aes_expand_key`, as emitted. -/
def expandKey : Prog isa := Impl.Scrub.X86.scrubF 0 532 (withStackScratchWiped 532 3 128 Impl.Aes.X86.expandKey)

/-- `vg_aes_expand_key_aesni`, as emitted. -/
def expandKeyAesni : Prog isa :=
  Impl.Scrub.X86.scrubF 0 532 (withStackScratchWiped 532 3 128 Impl.Aes.X86.AesNi.expandKey)

end VG.Impl.Aes.X86.Fn
