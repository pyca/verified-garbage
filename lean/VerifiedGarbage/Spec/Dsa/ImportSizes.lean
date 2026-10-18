module

/-!
# DSA import-size policy (trusted)

FIPS 186-4 §4.2 lists (1024,160), (2048,224), (2048,256), and
(3072,256). Legacy interoperability additionally requires (2048,160).
This extension applies to imported domain parameters, including key generation
from those parameters, signing, and verification. It does not change the
bits-only parameter generator's default subgroup sizes or certify primality.

These predicates are introduced separately from their adoption by the existing
DSA contracts and implementations, so the policy can be reviewed first.
-/

@[expose] public section
namespace VG.Spec.Dsa.Import

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

end VG.Spec.Dsa.Import
