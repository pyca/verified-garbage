module

public import VerifiedGarbage.Proof.Dsa.DomainShape
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.TCB.Artifact

/-! # Relating public width scans to the DSA parameter-size predicate -/

@[expose] public section

namespace VG.Proof.Dsa
open VG

theorem supported_scans (p q : List Byte) :
    Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ↔
    128 ≤ (significant p).2.toNat ∧ 128 ≤ (significant q).2.toNat ∧
      Spec.Dsa.supportedSizes (8 * (significant p).1) (8 * (significant q).1) := by
  have hp1 := significant_width p (n := 128) (by decide)
  have hp2 := significant_width p (n := 256) (by decide)
  have hp3 := significant_width p (n := 384) (by decide)
  have hq1 := significant_width q (n := 20) (by decide)
  have hq2 := significant_width q (n := 28) (by decide)
  have hq3 := significant_width q (n := 32) (by decide)
  have e : ∀ {a k : Nat}, 8 * a = 8 * k ↔ a = k := fun {_ _} => by omega
  -- Each width the predicate names is a scan's byte count and top bit, so
  -- after rewriting the goal is propositional (and `omega` would split on
  -- every `↔`).
  unfold Spec.Dsa.supportedSizes
  simp only [show (1024 : Nat) = 8 * 128 from rfl, show (2048 : Nat) = 8 * 256 from rfl,
    show (3072 : Nat) = 8 * 384 from rfl, show (160 : Nat) = 8 * 20 from rfl,
    show (224 : Nat) = 8 * 28 from rfl, show (256 : Nat) = 8 * 32 from rfl, hp1, hp2, hp3, hq1, hq2,
    hq3, e]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, (⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩)⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) <;> simp_all
  · rintro ⟨h1, h2, (⟨h3, h4⟩ | ⟨h3, (h4 | h4 | h4)⟩ | ⟨h3, h4⟩)⟩ <;> simp_all

/-- Supported subgroup widths are byte-aligned, including padded inputs. -/
theorem subgroup_scan_width {p q : List Byte}
    (h : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q))) :
    Spec.Dsa.bitLength (Spec.Dsa.decodeBE q) = 8 * (significant q).1 := by
  have hs := (supported_scans p q).mp h
  have hq1 := significant_width q (n := 20) (by decide)
  have hq2 := significant_width q (n := 28) (by decide)
  have hq3 := significant_width q (n := 32) (by decide)
  unfold Spec.Dsa.supportedSizes at h hs
  omega

/-- Only the last encoded byte determines whether a modulus is odd. -/
theorem decodeBE_last_mod_two (front : List Byte) (last : Byte) :
    Spec.Dsa.decodeBE (front ++ [last]) % 2 = last.toNat % 2 := by
  rw [decodeBE_append]
  have hlast : Spec.Dsa.decodeBE [last] = last.toNat := by simp [Spec.Dsa.decodeBE]
  rw [hlast]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.pow_one]
  rw [Nat.add_mod, Nat.mul_mod]
  simp

end VG.Proof.Dsa
