module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchSafety
public import VerifiedGarbage.Spec.Ffdh.GenerationContract

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchAbi
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchImplies

/-! # Verified complete native FFDH parameter generation for every arithmetic backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem search_verified (v : RoundImpl) : Verified target (searchCode v)
    (Spec.Ffdh.parameterSearchContract abi 160) := by
  exact Verified.of_correct (search_correct v) (search_constantTime v) search_implies

end VG.Proof.Ffdh.X86_64.Generation
