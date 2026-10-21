module

import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
public import Init.Prelude

/-! # Bounds for the compact paired-word product and unchanged operands -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact

/-- The product and multiplier use only 8N+28 bytes, rather than a separate
subtraction array. Prepared metadata precedes that writable range. -/
structure Lay (L N S mo a b : Nat) : Prop where
  header : 128 ≤ S
  scr : S + 8 * N + 28 ≤ L
  mo_le : mo + 4 * N ≤ L
  a_le : a + 4 * N ≤ L
  b_le : b + 4 * N ≤ L
  smo : mo + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ mo
  sa : a + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ a
  sb : b + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ b

end VG.Proof.Mont.X86.Compact
