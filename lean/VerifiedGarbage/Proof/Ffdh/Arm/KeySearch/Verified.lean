module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFunction
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Public
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Sat
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend

/-! Complete native ARMv7 key generation, including bounded retries and
entropy refills, satisfies the shared correctness and timing contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

theorem constantTime (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    ConstantTime isa (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pub
      (VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext (.call backend.keyName backend.generateKey)) := by
  intro s t tr₁ tr₂ u v hs ht pub e₁ e₂
  obtain ⟨p, inputS, inputT, statuses, sp⟩ := public_inputs hs ht pub
  exact (function_ct backend _ _ _ _ _ _
    ⟨(p, (searchResult p s).statuses), ⟨inputS, rfl⟩, ⟨inputT, statuses.symm⟩, sp⟩ e₁ e₂).1

/-- The native controller registered for this attempt backend. -/
def calledCode (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : Prog VG.Arm.isa :=
  VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext
    (.call backend.keyName backend.generateKey)

theorem verified (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    Verified target (VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext (.call backend.keyName backend.generateKey))
      (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)) :=
  ⟨correct backend, constantTime backend, sat⟩

end VG.Proof.Ffdh.Arm.KeySearch
