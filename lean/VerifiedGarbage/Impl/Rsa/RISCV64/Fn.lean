module

public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute
public import VerifiedGarbage.Impl.Bignum.RISCV64.PrivPre
public import VerifiedGarbage.Impl.Rsa.RISCV64.CrtValues
public import VerifiedGarbage.Impl.Rsa.RISCV64.CheckKey
public import VerifiedGarbage.Impl.Rsa.RISCV64.RecoverDet
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# RSA's key functions on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrub`):
the caller-saved registers cleared but the 32 bits of its result, and none
of the stack (these functions use none below the stack pointer that they do
not wipe themselves), so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_rsa_public_precompute`. -/
def publicPrecompute : Prog isa := scrub 32 0 Impl.Bignum.RISCV64.Precompute.precompute

/-- `vg_rsa_private_precompute`. -/
def privatePrecompute : Prog isa := scrub 32 0 Impl.Bignum.RISCV64.PrivPre.code

/-- `vg_rsa_crt_values`. -/
def crtValues : Prog isa := scrub 32 0 CrtValues.code

/-- `vg_rsa_check_key`. -/
def checkKey : Prog isa := scrub 32 0 CheckKey.code

/-- `vg_rsa_recover_primes_det`. -/
def recoverPrimesDet : Prog isa := scrub 32 0 RecoverDet.code

end VG.Impl.Rsa.RISCV64.Fn
