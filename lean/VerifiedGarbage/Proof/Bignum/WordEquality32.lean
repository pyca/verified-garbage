module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-! Equality of packed 32-bit integers is exactly equality of every limb. -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

/-- Splitting off the low word preserves equality of arbitrary equal-width arrays. -/
theorem val32_eq_iff_words (m : Mem) (base : Addr) (da db n : Nat) :
    val32 m base da n = val32 m base db n ↔
      ∀ j < n, m.readW (off base (da + 4 * j)) 32 = m.readW (off base (db + 4 * j)) 32 := by
  induction n generalizing da db with
  | zero => simp [val32]
  | succ n ih =>
    have la := (m.readW (off base da) 32).isLt
    have lb := (m.readW (off base db) 32).isLt
    have split : val32 m base da (n + 1) = val32 m base db (n + 1) ↔
        w32 m base da = w32 m base db ∧ val32 m base (da + 4) n = val32 m base (db + 4) n := by
      simp only [val32]
      simp only [w32]
      omega
    rw [split, ih]
    constructor
    · rintro ⟨head, tail⟩ j hj
      cases j with
      | zero => simpa only [Nat.mul_zero, Nat.add_zero] using BitVec.eq_of_toNat_eq head
      | succ j =>
        have eq := tail j (by omega)
        simpa only [show da + 4 + 4 * j = da + 4 * (j + 1) by omega,
          show db + 4 + 4 * j = db + 4 * (j + 1) by omega] using eq
    · intro all
      refine ⟨?_, ?_⟩
      · have eq := congrArg BitVec.toNat (all 0 (by omega))
        simpa only [Nat.mul_zero, Nat.add_zero] using eq
      · intro j hj
        have eq := all (j + 1) (by omega)
        simpa only [show da + 4 * (j + 1) = da + 4 + 4 * j by omega,
          show db + 4 * (j + 1) = db + 4 + 4 * j by omega] using eq
end VG.Proof.Bignum
