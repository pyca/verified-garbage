module

public import VerifiedGarbage.Impl.AesGcm.X86_64.Short
public import VerifiedGarbage.Impl.Aes.X86_64.AesNi

/-!
# AES-GCM on x86-64: `seal` ending without calls, with AES-NI

`seal` for the instances whose CPUs have AES-NI, PCLMULQDQ and AVX but not
the AVX-512 of `Short`: the other instances' body (`Impl.AesGcm.X86_64.seal`)
up to the whole blocks, then `Short.finishWith Short.finKsA`: the bytes
left, the lengths block and the tag without calls, as `Short.seal`'s long
path ends, with the keystream of `J₀` and of the counter block computed with
AES-NI on 128-bit registers.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.SealFin

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ Callees tagOut restore oneEntry oneAad oneBlocks)

/-- `seal`'s body after the entry. -/
def mid (c : Callees) : Prog isa :=
  .seq (oneAad c) (.seq (oneBlocks c.enc) (Short.finishWith Short.finKsA))

/-- `vg_aes_gcm_seal`, ending without calls. -/
def «seal» (c : Callees) : Prog isa :=
  .seq (.block (oneEntry 32)) (.seq (mid c) (.seq (.block (tagOut (at_ .rsp 24))) (.block restore)))

end VG.Impl.AesGcm.X86_64.SealFin
