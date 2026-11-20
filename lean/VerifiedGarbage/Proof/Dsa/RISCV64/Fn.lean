module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Fn
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParameterSearchInit
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Instances
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
public import VerifiedGarbage.Proof.Dsa.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-!
# DSA on RISC-V, as emitted

Key derivation and generation, the validation of keys, signing and
verification, and the parameter search's start, with their cleanup
(`Impl.Dsa.RISCV64.Fn`): each meets its contract in constant time and
returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbed`), which is what its registration binds. What
the cleanup needs of each function's code (`Scrub.scrubSide`) is evaluated
here, by the kernel.

The parameter search, `vg_dsa_parameter_search`, is generic over the
Miller-Rabin round (`Proof.Variants.MillerRabin.RISCV64`): what its cleanup
needs of its code (`Scrub.scrubSide`: the depth of its frames, and that it
calls nothing indirectly) does not yet follow from what each round proves of
its own code, so its registrations are still built here with
`RISCV64.Scrub.scrubOf` (`PSearch.parameterSearchSide`), for its
registration file to bind.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Dsa.RISCV64.Scrub
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

theorem deriveKey :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.deriveKey (Spec.Dsa.deriveKeyContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.deriveKeyApi) (W := 0)
    { code := Impl.Dsa.RISCV64.Derive.derive, verified := deriveKey_verified }
    (deriveKeyOut _ []) (by lit_decide)

theorem validatePrivateKey :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.validatePrivateKey
      (Spec.Dsa.validatePrivateKeyContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePrivateKeyApi) (W := 0)
    { code := Impl.Dsa.RISCV64.PrevalidatedSign.validate, verified := validatePrivate_verified }
    (validatePrivateKeyOut _ []) (by lit_decide)

theorem randomSignPrevalidated :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.randomSignPrevalidated
      (Spec.Dsa.randomSignPrevalidatedContract abi 192) 32 :=
  verifiedScrubbed (api := Spec.Dsa.randomSignPrevalidatedApi) (W := 192)
    { code := Impl.Dsa.RISCV64.PrevalidatedSign.randomSign, verified := randomSignPre_verified }
    (randomSignPrevalidatedOut _ []) (by lit_decide)

theorem generateKey :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.generateKey (Spec.Dsa.generateKeyContract abi 192) 32 :=
  verifiedScrubbed (api := Spec.Dsa.generateKeyApi) (W := 192)
    { code := Impl.Dsa.RISCV64.Generate.code, verified := generateKey_verified }
    (generateKeyOut _ []) (by lit_decide)

theorem validatePublicKey :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.validatePublicKey
      (Spec.Dsa.validatePublicKeyContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePublicKeyApi) (W := 0)
    { code := Impl.Dsa.RISCV64.Prevalidated.validate, verified := validate_verified }
    (validatePublicKeyOut _ []) (by lit_decide)

theorem verifyPrevalidated :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.verifyPrevalidated
      (Spec.Dsa.verifyPrevalidatedContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.verifyPrevalidatedApi) (W := 0)
    { code := Impl.Dsa.RISCV64.Prevalidated.verify, verified := prevalidated_verified }
    (verifyPrevalidatedOut _ []) (by lit_decide)

theorem parameterInit :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.parameterInit (Spec.Dsa.parameterInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.parameterInitApi) (W := 0)
    { code := Impl.Dsa.RISCV64.ParameterSearch.init, verified := init_verified }
    (parameterInitOut []) (by lit_decide)

/-- `vg_dsa_parameter_search` over each Miller-Rabin round, scrubbed. -/
def parameterSearchRegs : List (Registration Spec.Dsa.parameterSearchApi RISCV64.target) :=
  Proof.Variants.MillerRabin.RISCV64.variants.attach.map
    fun (v : { v : RoundImpl // v ∈ Proof.Variants.MillerRabin.RISCV64.variants }) =>
      scrubOf {
        suffix := v.1.suffix
        code := Impl.Dsa.RISCV64.ParameterSearch.code (PSearch.gen1 v.1) (PSearch.gen2 v.1) (PSearch.gen3 v.1)
        verified := PSearch.params_verified v.1 }
        (parameterSearchOut 512 PSearch.kT) 512 (Spec.Dsa.parameterSearchSig.retBits 64)
        (PSearch.parameterSearchSide v.1 v.2)

end VG.Proof.Dsa.RISCV64.Fn
