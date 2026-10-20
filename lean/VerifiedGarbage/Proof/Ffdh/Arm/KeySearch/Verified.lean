module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFunction
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Public
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Sat
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.Backend

/-! Complete native ARMv7 key generation, including bounded retries and
entropy refills, satisfies the shared correctness and timing contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Spec.Ffdh

theorem constantTime (backend : VG.Proof.Ffdh.Arm.Backend) :
    ConstantTime isa (keySearchContract abi stackUse).pre (keySearchContract abi stackUse).pub
      (VG.Impl.Ffdh.Arm.KeySearch.code (.call backend.keyName backend.generateKey)) := by
  intro s t tr₁ tr₂ u v hs ht pub e₁ e₂
  obtain ⟨p, inputS, inputT, statuses, sp⟩ := public_inputs hs ht pub
  exact (function_ct backend _ _ _ _ _ _
    ⟨(p, (searchResult p s).statuses), ⟨inputS, rfl⟩, ⟨inputT, statuses.symm⟩, sp⟩ e₁ e₂).1

theorem verified (backend : VG.Proof.Ffdh.Arm.Backend) :
    Verified target (VG.Impl.Ffdh.Arm.KeySearch.code (.call backend.keyName backend.generateKey))
      (keySearchContract abi stackUse) :=
  ⟨correct backend, constantTime backend, sat⟩

end VG.Proof.Ffdh.Arm.KeySearch
