module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
public import VerifiedGarbage.Proof.Bignum.Amm52
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubCT
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedBackend
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubCode

/-! # `vg_rsa_public_precomputed_checked_ifma`: `Verified` -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma.Pub
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem ifma_verified : Verified target (Impl.Rsa.X86_64.PubIfma.checked Mont.adxSquare.mm)
    (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  Verified.of_correct (k := pdChkContract) (checked_correct Mont.adxSquare (by decide +kernel))
    (checked_ct Mont.adxSquare FoldedPublic.adx_final_ct) precomputedChecked_implies

end VG.Proof.Bignum.X86_64.Ifma.Pub
