module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Instances
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.Verified
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBase
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTCode
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64
import VerifiedGarbage.Proof.Framework.Lit

/-!
# FFDH on AArch64: what `scrubAllOf` needs of its scrubbed functions

`ScrubAll.scrubSide` of each function the registration file scrubs, with the
registers its tail clears (`Scrub.clearMul`, `Scrub.clearWindow`): evaluated
here, by the kernel, so that the emitter works out nothing.
-/

-- separate module: the kernel's evaluation of the scrub's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

/-- Of `vg_ffdh_generate_key_search_cached`. -/
theorem cachedKeySearchSide :
    scrubSide (Proof.Ffdh.AArch64.Cached.cachedSearch)
      64 (Spec.Ffdh.cachedKeySearchSig.retBits abi.ptrBits) clearMul [] = true := by lit_decide

/-- Of `vg_ffdh_check_public`. -/
theorem checkPublicSide :
    scrubSide (Impl.Ffdh.AArch64.Domain.CheckPublic.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm)
      0 (Spec.Ffdh.checkPublicSig.retBits abi.ptrBits) clearWindow [] = true := by lit_decide

/-- Of `vg_ffdh_exchange`. -/
theorem exchangeSide :
    scrubSide (Impl.Ffdh.AArch64.Domain.Exchange.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm)
      0 (Spec.Ffdh.exchangeSig.retBits abi.ptrBits) clearWindow [] = true := by lit_decide

/-- Of `vg_ffdh_check_private`. -/
theorem checkPrivateSide :
    scrubSide (Impl.Ffdh.AArch64.Domain.CheckPrivate.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm)
      0 (Spec.Ffdh.checkPrivateSig.retBits abi.ptrBits) clearWindow [] = true := by lit_decide

/-- Of `vg_ffdh_derive_public`. -/
theorem derivePublicSide :
    scrubSide (Impl.Ffdh.AArch64.Domain.DerivePublic.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm)
      0 (Spec.Ffdh.derivePublicSig.retBits abi.ptrBits) clearWindow [] = true := by lit_decide

/-- Of `vg_ffdh_generate_parameters`, with each implementation of the
Miller–Rabin round. -/
theorem sievedParameterSearchSide (v : Proof.MillerRabin.AArch64.RoundImpl) (hv : v ∈ Proof.Variants.MillerRabin.AArch64.variants) :
    scrubSide (Proof.Ffdh.AArch64.Generation.searchCode v)
      (Proof.Ffdh.AArch64.Generation.stackUse) (Spec.Ffdh.parameterSearchSig.retBits abi.ptrBits) clearMul [] = true := by
  have e : (Proof.Variants.MillerRabin.AArch64.variants.all fun v => 
      scrubSide (Proof.Ffdh.AArch64.Generation.searchCode v)
      (Proof.Ffdh.AArch64.Generation.stackUse) (Spec.Ffdh.parameterSearchSig.retBits abi.ptrBits) clearMul []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.Ffdh.AArch64.Scrub
