module

public import VerifiedGarbage.Impl.AesCbc.X86
public import VerifiedGarbage.Impl.CallWipe.X86
public import VerifiedGarbage.Impl.Zeroize.X86

/-!
# AES-CBC on x86, zeroing its scratch

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` for a blocks implementation
`b` that writes only the first `w` bytes of its working space: the CBC code
around `b` that zeroes what it saves in `scratch` (`encryptZ`, `decryptZ` in
`Impl/AesCbc/X86.lean`), which leaves of `scratch` only those `w` bytes
changed; where `w = 0`, that code itself, and otherwise a call of it (the
internal functions `vg_aes_cbc_encrypt_unwiped` and
`vg_aes_cbc_decrypt_unwiped`, with the variant's suffix), then of
`vg_zeroize` on the first `w` bytes of `scratch` (the sixth argument).
-/

@[expose] public section

namespace VG.Impl.AesCbc.X86.Wiped

open VG.X86
open VG.Impl.Aes.X86 (Blocks)

/-- A call of `name`, whose code is `body`, with the six stack arguments,
then of `vg_zeroize` on the first `n` bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) (n : Nat) : Prog isa :=
  Impl.CallWipe.X86.callWipe 6 5 n name body "vg_zeroize" Impl.Zeroize.X86.zeroize

/-- `vg_aes_cbc_encrypt` around `b`, whose variant's suffix is `suffix`,
zeroing the first `w` bytes of `scratch`. -/
def encrypt (b : Blocks) (suffix : String) (w : Nat) : Prog isa :=
  wiped ("vg_aes_cbc_encrypt_unwiped" ++ suffix) (Impl.AesCbc.X86.encryptZ b) w

/-- `vg_aes_cbc_decrypt` around `b`, whose variant's suffix is `suffix`,
zeroing the first `w` bytes of `scratch`. -/
def decrypt (b : Blocks) (suffix : String) (w : Nat) : Prog isa :=
  wiped ("vg_aes_cbc_decrypt_unwiped" ++ suffix) (Impl.AesCbc.X86.decryptZ b) w

end VG.Impl.AesCbc.X86.Wiped
