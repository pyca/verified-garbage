module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontSave
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Bignum.Minv32`, which this module and modules that import it used -/

section

/-!
# `-m⁻¹ mod 2³²` from `-m⁻¹ mod 2⁶⁴`, on any target

The RSA working space's header holds `-m⁻¹ mod 2⁶⁴`; code that reads its low
32 bits has `-m⁻¹ mod 2³²` for `m`'s low 32 bits (`minv_low`).
-/

@[expose] public section

namespace VG.Proof.Bignum.Minv32

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2³²`, for the low digits. -/
theorem minv_low {m minv : Nat} (h : (m * minv + 1) % 2 ^ 64 = 0) :
    (m % 2 ^ 32 * (minv % 2 ^ 32) + 1) % 2 ^ 32 = 0 := by
  have h' : (m * minv + 1) % 2 ^ 32 = 0 := by
    have := Nat.mod_mod_of_dvd (m * minv + 1) (show 2 ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by decide⟩)
    rw [← this, h]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  exact h'

end VG.Proof.Bignum.Minv32

end

end

/-!
# Montgomery multiplication on PPC64LE: the function

`vg_rsa_mont_mul(ws = r3, ws_len = r4, o = r5, a = r6, b = r7, scratch = r8)`
saves the nonvolatile registers in the scratch buffer, runs the arithmetic
(`core_ok`) and restores them. `numAt_eq`: a number of the working space
as the proofs read it.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

/-- A number of the working space is its `2 w` digits. -/
theorem numAt_eq (m : Mem) (B : Addr) (w j : Nat) : numAt m B w j = val32 m B (slot w j) (2 * w) := by
  rw [← wordsVal_eq_val32, ← read_eq_wordsVal]; rfl

end VG.Proof.Bignum.PPC64LE
