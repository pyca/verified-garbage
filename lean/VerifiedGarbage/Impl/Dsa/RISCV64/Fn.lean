module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Derive
public import VerifiedGarbage.Impl.Dsa.RISCV64.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.RISCV64.Generate
public import VerifiedGarbage.Impl.Dsa.RISCV64.Prevalidated
public import VerifiedGarbage.Impl.Dsa.RISCV64.ParameterSearch
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# DSA on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrub`):
the caller-saved registers cleared but the 32 bits of its result, and the
stack its frames use (192 bytes for signing and key generation, none for
the others), so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_dsa_derive_key`. -/
def deriveKey : Prog isa := scrub 32 0 Derive.derive

/-- `vg_dsa_validate_private_key`. -/
def validatePrivateKey : Prog isa := scrub 32 0 PrevalidatedSign.validate

/-- `vg_dsa_sign_random_prevalidated`. -/
def randomSignPrevalidated : Prog isa := scrub 32 192 PrevalidatedSign.randomSign

/-- `vg_dsa_generate_key`. -/
def generateKey : Prog isa := scrub 32 192 Generate.code

/-- `vg_dsa_validate_public_key`. -/
def validatePublicKey : Prog isa := scrub 32 0 Prevalidated.validate

/-- `vg_dsa_verify_prevalidated`. -/
def verifyPrevalidated : Prog isa := scrub 32 0 Prevalidated.verify

/-- `vg_dsa_parameter_search_init`. -/
def parameterInit : Prog isa := scrub 32 0 ParameterSearch.init

end VG.Impl.Dsa.RISCV64.Fn
