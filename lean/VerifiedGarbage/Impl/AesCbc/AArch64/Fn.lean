module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
public import VerifiedGarbage.Impl.AesCbc.AArch64.Encrypt
public import VerifiedGarbage.Impl.CallWipe.AArch64
public import VerifiedGarbage.Impl.Zeroize.AArch64Wide
public import VerifiedGarbage.Impl.Scrub.AArch64.Writes
public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# AesCbc on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/AesCbc/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.AesCbc.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64

/-- The vector registers the decryptions leave secrets in. -/
def left : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24,
   .v25, .v26, .v27, .v28, .v29, .v30, .v31]

/-- `codeAes`, then `left` cleared. -/
def decryptAes : Prog isa := withClears [] left none Impl.AesCbc.AArch64.Decrypt.codeAes

/-- `code`, then `left` cleared. -/
def decrypt : Prog isa := withClears [] left none Impl.AesCbc.AArch64.Decrypt.code

/-- `vg_aes_cbc_encrypt_aes`: the encryption with the AES instructions, which
has no frames and writes nothing in `scratch`, then the registers it writes
cleared. -/
def encryptAes : Prog isa := scrubOf 0 0 Impl.AesCbc.AArch64.Encrypt.code

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2176 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.AArch64.callWipe .x5 2176 name body "vg_zeroize" Impl.Zeroize.AArch64.zeroizeWide

/-- `vg_aes_cbc_encrypt<suffix>` for an implementation that writes in
`scratch`: a call of its encryption `body`, `scratch` wiped, then the cleanup
that clears the registers that code writes and zeroes its 32 bytes of stack. -/
def encrypt (suffix : String) (body : Prog isa) : Prog isa :=
  scrubOf 32 0 (wiped ("vg_aes_cbc_encrypt_unwiped" ++ suffix) body)

/-- `vg_aes_cbc_decrypt<suffix>` for an implementation that writes in
`scratch`, likewise. -/
def decryptWiped (suffix : String) (body : Prog isa) : Prog isa :=
  scrubOf 32 0 (wiped ("vg_aes_cbc_decrypt_unwiped" ++ suffix) body)

end VG.Impl.AesCbc.AArch64.Fn
