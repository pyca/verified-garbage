module

public import VerifiedGarbage.Impl.AesCbc.X86
public import VerifiedGarbage.Impl.CallWipe.X86
public import VerifiedGarbage.Impl.Zeroize.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# AES-CBC on x86, zeroing its scratch

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` for a blocks implementation
`b` that writes only the first `w` bytes of its working space: the CBC code
around `b` that zeroes what it saves in `scratch` (`encryptZ`, `decryptZ` in
`Impl/AesCbc/X86.lean`), which leaves of `scratch` only those `w` bytes
changed; where `w = 0`, that code itself, and otherwise a call of it (the
internal functions `vg_aes_cbc_encrypt_unwiped` and
`vg_aes_cbc_decrypt_unwiped`, with the variant's suffix), then of
`vg_zeroize`'s code (the internal `vg_zeroize_core`) on the first `w` bytes
of `scratch` (the sixth argument).
With AES-NI the CBC code is not around `b`: decryption's is that of
`Impl/AesCbc/X86/Decrypt.lean`, which writes only the first 240 bytes of
`scratch`, wrapped the same way, and encryption's is `encryptNi`, which
writes none and is not wrapped.
-/

@[expose] public section

namespace VG.Impl.AesCbc.X86.Wiped

open VG.X86
open VG.Impl.Aes.X86 (Blocks)

/-- A call of `name`, whose code is `body`, with the six stack arguments,
then of `vg_zeroize`'s code (the internal `vg_zeroize_core`) on the first
`n` bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) (n : Nat) : Prog isa :=
  Impl.CallWipe.X86.callWipe 6 5 n name body "vg_zeroize_core" Impl.Zeroize.X86.zeroize

/-- `vg_aes_cbc_encrypt` with the CBC code `body` (`encryptZ` around a blocks
implementation, or `encryptNi`), whose variant's suffix is `suffix`,
zeroing the first `w` bytes of `scratch`. -/
def encrypt (body : Prog isa) (suffix : String) (w : Nat) : Prog isa :=
  wiped ("vg_aes_cbc_encrypt_unwiped" ++ suffix) body w

/-- `vg_aes_cbc_decrypt` with the CBC code `body` (`decryptZ` around a blocks
implementation, or the code of `Impl/AesCbc/X86/Decrypt.lean`), whose
variant's suffix is `suffix`, zeroing the first `w` bytes of `scratch`. -/
def decrypt (body : Prog isa) (suffix : String) (w : Nat) : Prog isa :=
  wiped ("vg_aes_cbc_decrypt_unwiped" ++ suffix) body w

end VG.Impl.AesCbc.X86.Wiped

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF 0 W`): the `W`
bytes of stack below `esp` that it and its callees use zeroed, and the
registers a callee may change cleared, so that it returns without secret
residue. -/

namespace VG.Impl.AesCbc.X86.Fn

open VG.X86

/-- `vg_aes_cbc_encrypt` or `vg_aes_cbc_decrypt` as the CBC code `body`
itself, where it writes nothing in `scratch`, as emitted. -/
def free (body : Prog isa) : Prog isa := Impl.Scrub.X86.scrubF 0 24 body

/-- `vg_aes_cbc_encrypt` as the call of the CBC code `body`, then of
`vg_zeroize` on the first `w` bytes of `scratch` (`Wiped.encrypt`), as
emitted. -/
def encrypt (body : Prog isa) (suffix : String) (w : Nat) : Prog isa :=
  Impl.Scrub.X86.scrubF 0 72 (Impl.AesCbc.X86.Wiped.encrypt body suffix w)

/-- `vg_aes_cbc_decrypt` as the call of the CBC code `body`, then of
`vg_zeroize` on the first `w` bytes of `scratch` (`Wiped.decrypt`), as
emitted. -/
def decrypt (body : Prog isa) (suffix : String) (w : Nat) : Prog isa :=
  Impl.Scrub.X86.scrubF 0 72 (Impl.AesCbc.X86.Wiped.decrypt body suffix w)

end VG.Impl.AesCbc.X86.Fn
