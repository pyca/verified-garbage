module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Implies
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.CT
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_generate_key` on PPC64LE: verified against the shared contract

With correctness (`gk_correct`), constant time (`gk_ct`) and the shared
contract (`gk_implies`), `generateKey` is verified (`gk_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Ffdh.PPC64LE.GenerateKey

/-- `vg_ffdh_generate_key`. -/
theorem gk_verified : Verified target generateKey (Spec.Ffdh.generateKeyContract abi) :=
  Verified.of_correct gk_correct gk_ct gk_implies

end VG.Proof.Ffdh.PPC64LE.GenerateKey
