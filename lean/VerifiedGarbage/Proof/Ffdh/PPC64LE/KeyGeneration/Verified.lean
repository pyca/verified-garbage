module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Contract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Correct
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.CT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.CT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Implies

/-! # The verified key search (PPC64LE)

For any attempt that uses no stack of its own (`key_verified_of`), and for
the one `Artifacts/Ffdh/PPC64LE.lean` registers: `vg_ffdh_generate_key`
(`baseAttempt`, `key_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE

theorem key_verified_of (a : Attempt) :
    Verified target (Impl.Ffdh.PPC64LE.KeyGeneration.Search.code a.call)
      (Spec.Ffdh.keySearchContract abi stackUse) :=
  Verified.of_correct (key_correct a) (key_constantTime a) key_implies

/-- The registered `vg_ffdh_generate_key`, which has no frames. -/
def baseAttempt : Attempt where
  name := Spec.Ffdh.generateKeyApi.name
  code := Impl.Ffdh.PPC64LE.GenerateKey.generateKey
  stack := by decide +kernel
  correct := GenerateKey.gk_correct
  ct := GenerateKey.gk_ct

/-- The key search calling it. -/
abbrev keyCode : Prog isa := Impl.Ffdh.PPC64LE.KeyGeneration.Search.code baseAttempt.call

theorem key_verified : Verified target keyCode (Spec.Ffdh.keySearchContract abi stackUse) :=
  key_verified_of baseAttempt

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
