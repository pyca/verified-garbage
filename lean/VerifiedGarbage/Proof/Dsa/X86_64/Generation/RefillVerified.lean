module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillBackend
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCT
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # The x86-64 DSA parameter search over refillable tapes, verified

`RefillBackend.searchCode_verified` with the per-width constant-time proof
(`refill_ct`), and the pairs of a SHA-1 and a SHA-256 implementation that
the search is emitted for (`hashPairs`). Separate from both so that the
correctness and constant-time proofs build in parallel. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.RefillBackend

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem refillCT : RefillCTObligation := fun checkName H M Sq T pBytes hp =>
  VG.Proof.Dsa.X86_64.Generation.refill_ct (checkName := checkName) H M Sq T pBytes _ hp rfl

theorem search_verified (v1 v256 : Proof.Pbkdf2.Md.X86_64.MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target (searchCode v1 v256 v) (Spec.Dsa.parameterSearchContract abi 632) :=
  searchCode_verified refillCT v1 v256 v h1 h256

/-- A SHA-1 and a SHA-256 implementation, as the parameter search takes
them, and that they are SHA-1 and SHA-256. -/
structure Hashes where
  sha1 : Proof.Pbkdf2.Md.X86_64.MdHash
  sha256 : Proof.Pbkdf2.Md.X86_64.MdHash
  h1 : sha1.mgf.G.rust = "sha1"
  h256 : sha256.mgf.G.rust = "sha256"

open VG.Proof.Variants.MdHash.X86_64 (sha1Variants sha256Variants)

theorem sha1Variants_rust : ∀ v ∈ sha1Variants, v.mgf.G.rust = "sha1" := by
  intro v hv
  simp only [sha1Variants, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> rfl

theorem sha256Variants_rust : ∀ v ∈ sha256Variants, v.mgf.G.rust = "sha256" := by
  intro v hv
  simp only [sha256Variants, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> rfl

/-- The pairs the parameter search is emitted for, best first: a SHA-1 and
a SHA-256 implementation for the same CPUs (both baselines, both SHA
extensions, or SHA-1's AVX and BMI code with SHA-256's AVX2 code, BMI2
coming only with AVX2). Any other pair needs the features of one of these,
which runs both hashes with them. -/
def hashPairs : List Hashes :=
  sha1Variants.attach.flatMap fun ⟨v1, h1⟩ => sha256Variants.attach.filterMap fun ⟨v256, h256⟩ =>
    if v1.suffix == v256.suffix || (v1.suffix == "_avx_bmi" && v256.suffix == "_avx2") then
      some ⟨v1, v256, sha1Variants_rust v1 h1, sha256Variants_rust v256 h256⟩
    else none

end VG.Proof.Dsa.X86_64.Generation.RefillBackend
