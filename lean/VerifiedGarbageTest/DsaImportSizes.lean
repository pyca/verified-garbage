module

import VerifiedGarbage.Spec.Dsa.Generate
meta import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.TCB.Audit
meta import VerifiedGarbage.TCB.Audit

/-! Regression checks for the trusted legacy DSA import-size policy:
`supportedSizes` and `lengthsValid` accept exactly the FIPS 186-4 §4.2
pairs and the legacy (2048,160) pair, stated below as `Import.sizesValid`
and `Import.lengthsValid`, and parameter generation does not. -/
namespace VG.Test.DsaImportSizes
open Spec.Dsa

namespace Import

/-- Accepted actual (p,q) bit lengths, including the legacy 2048/160 pair. -/
def sizesValid (l n : Nat) : Prop :=
  (l = 1024 ∧ n = 160) ∨ (l = 2048 ∧ (n = 160 ∨ n = 224 ∨ n = 256)) ∨
    (l = 3072 ∧ n = 256)

instance (l n : Nat) : Decidable (sizesValid l n) := by
  unfold sizesValid
  infer_instance

/-- Accepted external (p,q) byte widths. Leading-zero padding is allowed;
actual domain sizes are checked separately with `sizesValid`. -/
def lengthsValid (pLen qLen : Nat) : Prop :=
  (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ (qLen = 20 ∨ qLen = 28 ∨ qLen = 32)) ∨
    (pLen = 384 ∧ qLen = 32)

instance (pLen qLen : Nat) : Decidable (lengthsValid pLen qLen) := by
  unfold lengthsValid
  infer_instance

end Import

-- The contracts adopt exactly the import policy.
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

#guard supportedSizes 2048 160
#guard lengthsValid 256 20
#guard ¬supportedSizes 1024 224
#guard ¬supportedSizes 3072 160
#guard ¬lengthsValid 128 28
#guard ¬lengthsValid 384 20

-- The import extension does not enable parameter generation at 2048/160.
#guard ¬generationLengthsValid 256 20

#assert_spec_origin

end VG.Test.DsaImportSizes
