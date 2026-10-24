module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Implies
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_derive_public` on PPC64LE: verified against the shared contract

With correctness (`dp_correct`), constant time (`dp_ct`) and the shared
contract (`dp_implies`), `derivePublic` is verified (`dp_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Derive

open VG VG.PPC64LE VG.Impl.Ffdh.PPC64LE.Derive

/-- `vg_ffdh_derive_public`. -/
theorem dp_verified : Verified target derivePublic (Spec.Ffdh.derivePublicContract abi) :=
  Verified.of_correct dp_correct dp_ct dp_implies

end VG.Proof.Ffdh.PPC64LE.Derive
