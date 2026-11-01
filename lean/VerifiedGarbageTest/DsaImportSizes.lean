module

import VerifiedGarbage.Spec.Dsa.ImportSizes
meta import VerifiedGarbage.Spec.Dsa.ImportSizes
import VerifiedGarbage.Spec.Dsa.Generate
meta import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit
meta import VerifiedGarbage.TCB.Audit

/-! Regression checks for the trusted legacy DSA import-size policy. -/
namespace VG.Test.DsaImportSizes
open Spec.Dsa

-- Existing contracts now adopt exactly the separately reviewed import policy.
example (l n : Nat) : supportedSizes l n ↔ Import.sizesValid l n := Iff.rfl
example (pLen qLen : Nat) : lengthsValid pLen qLen ↔ Import.lengthsValid pLen qLen := Iff.rfl

-- Exactly the four FIPS pairs and the additional legacy pair are accepted.
example (l n : Nat) : Import.sizesValid l n ↔
    (l, n) = (1024, 160) ∨ (l, n) = (2048, 160) ∨
    (l, n) = (2048, 224) ∨ (l, n) = (2048, 256) ∨ (l, n) = (3072, 256) := by
  simp only [Import.sizesValid, Prod.mk.injEq]
  omega

example (pLen qLen : Nat) : Import.lengthsValid pLen qLen ↔
    Import.sizesValid (8 * pLen) (8 * qLen) := by
  unfold Import.lengthsValid Import.sizesValid
  omega

#guard Import.sizesValid 2048 160
#guard Import.lengthsValid 256 20
#guard ¬Import.sizesValid 1024 224
#guard ¬Import.sizesValid 3072 160
#guard ¬Import.lengthsValid 128 28
#guard ¬Import.lengthsValid 384 20

-- The import extension does not enable parameter generation at 2048/160.
#guard subgroupBits 2048 == some 256
#guard ¬generationLengthsValid 256 20
#guard generateParametersBytes 256 20 [] [] [] == none

#assert_standard_axioms Import.sizesValid
#assert_standard_axioms Import.lengthsValid
#assert_no_compiler_overrides Import.sizesValid Import.lengthsValid
#assert_spec_origin

end VG.Test.DsaImportSizes
