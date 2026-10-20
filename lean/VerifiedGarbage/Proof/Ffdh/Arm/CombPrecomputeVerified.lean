module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeContractCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSat

/-! The complete public comb initializer meets its separately reviewed contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem combPrecompute_verified (backend : MontBackend) :
    Verified target (VG.Impl.Ffdh.Arm.CombPrecompute.code
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code)
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176) :=
  ⟨combPrecompute_correct backend,
    combPrecompute_contract_ct backend (CombBuilder.main_ct backend),combPrecompute_sat⟩

/-- The caller transform is part of the registered initializer. -/
def combPrecomputeCalledCode (backend : MontBackend) : Prog isa :=
  backend.caller.code (VG.Impl.Ffdh.Arm.CombPrecompute.code
    (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code)

theorem combPrecomputeCalled_verified (backend : MontBackend) :
    Verified target (combPrecomputeCalledCode backend)
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176) :=
  backend.caller.verified (combPrecompute_verified backend)

end VG.Proof.Ffdh.Arm
