module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery multiplication on PPC64LE: saving and restoring the nonvolatile registers

The function stores `r14`–`r22` in the 72-byte scratch buffer at `r8`, and
copies its address into `r21`, then loads them back through `r21`, `r21`
last: where they are saved (`savR`), apart from each other and the working
space.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE

/-- The scratch buffer, 72 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 72⟩

theorem saved_inj : ∀ i < 9, ∀ j < 9, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 8, saved i ≠ .r21 := by decide

theorem saved_8 : saved 8 = .r21 := rfl

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 9) : (savR w).Contains (off w (8 * i)) 8 :=
  Offset.contains_base w (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 9) (hj : j < 9) (h : i ≠ j) :
    Mem.Sep (off w (8 * i)) 8 (off w (8 * j)) 8 :=
  Offset.sep w (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

end VG.Proof.Bignum.PPC64LE
