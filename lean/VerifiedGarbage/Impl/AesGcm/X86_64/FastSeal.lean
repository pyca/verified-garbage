module

public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
import VerifiedGarbage.Impl.AesGcm.X86_64.SealFin

/-!
# AES-GCM on x86-64: `seal`'s path for TLS records

`vg_aes_gcm_seal_prepared` with a prepared key context
(`VG.Spec.Gcm.PreparedPowersRepr`) takes a path of its own for the records of
TLS too long for the short path: a 12-byte nonce and at most 16 bytes of
additional data (`Fast.cond`). It is the other instances' body
(`Short.sealLong`) with the additional data absorbed with the prepared `H'`
(`Fast.aad`), where `oneAad` would copy it a byte at a time and call
`vg_ghash`, which computes `H'` from `H` on every call; for the instances
without the short path, `SealFin.mid` likewise, with `Short.finKsA`.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.FastSeal

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (Callees oneBlocks)

variable (c : Callees)

/-- After the entry: `Short.sealLong` with `Fast.aad`, the keystream of `J₀`
and of the counter block from `ks` (`Short.finKs` on 512-bit registers,
`Short.finKsA` on 128-bit ones). -/
def run (ks : Prog isa := Short.finKs) : Prog isa :=
  .seq Fast.aad (.seq (oneBlocks c.enc) (Short.finishWith ks))

/-- `Fast.cond any`, then this path, or `other`. -/
def sel (other : Prog isa) (ks : Prog isa := Short.finKs) (any : Bool := false) : Prog isa :=
  .seq (Fast.cond any) (.ite .e other (run c ks))

end VG.Impl.AesGcm.X86_64.FastSeal
