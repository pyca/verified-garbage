module

public import VerifiedGarbage.Impl.Rsa.AArch64
public import VerifiedGarbage.Impl.Rsa.AArch64.PrivPre
public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Impl.Rsa.AArch64.RecoverDet
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightCall
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-!
# RSA's key functions on AArch64, as emitted

Each function is its code, then its cleanup: the registers it writes that the
calling convention does not preserve, stated here, are cleared, but the 32
bits of its result (`Impl.Residue.AArch64.scrubAll`; these functions use no
stack beyond what they wipe themselves), so that it returns without secret
residue. The two precomputations multiply with the Montgomery product the
other RSA functions use (`Impl.Bignum.AArch64.SquareEightCall.mm`).
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64 (scrubAll)

/-- `vg_rsa_public_precompute`. -/
def publicPrecompute : Prog isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v31],
     []⟩
    (Precompute.code Impl.Bignum.AArch64.SquareEightCall.mm)

/-- `vg_rsa_private_precompute`. -/
def privatePrecompute : Prog isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v31],
     []⟩
    (PrivPre.code Impl.Bignum.AArch64.SquareEightCall.mm)

/-- `vg_rsa_crt_values`. -/
def crtValues : Prog isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26],
     []⟩
    Keys.CrtValues.code

/-- `vg_rsa_recover_primes_det`. -/
def recoverPrimesDet : Prog isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26],
     []⟩
    RecoverDet.code

/-- `vg_rsa_check_key`. -/
def checkKey : Prog isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [],
     []⟩
    CheckKey.code

end VG.Impl.Rsa.AArch64.Fn
