module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillBackend
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCT

/-! # The x86-64 DSA parameter search over refillable tapes, verified

`RefillBackend.searchCode_verified` with the per-width constant-time proof
(`refill_ct`). Separate from both so that the correctness and
constant-time proofs build in parallel. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.RefillBackend

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem refillCT : RefillCTObligation := fun checkName H M Sq T pBytes hp =>
  VG.Proof.Dsa.X86_64.Generation.refill_ct (checkName := checkName) H M Sq T pBytes _ hp rfl

theorem search_verified (v1 v256 : Proof.Pbkdf2.Md.X86_64.MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target (searchCode v1 v256 v) (Spec.Dsa.parameterSearchContract abi 632) :=
  searchCode_verified refillCT v1 v256 v h1 h256

end VG.Proof.Dsa.X86_64.Generation.RefillBackend
