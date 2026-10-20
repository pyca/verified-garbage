module

public import VerifiedGarbage.Proof.MillerRabin.X86.Core
import VerifiedGarbage.Proof.MillerRabin.X86.ExponentMath
import VerifiedGarbage.Proof.MillerRabin.TableCongr32

/-! # The complete native-window result is the reviewed Miller–Rabin test -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem finishedState_eq {A : Nat → Nat} {c w b : Nat}
    (odd : c % 2 = 1) (minimum : 3 ≤ c) (fits : c < 2 ^ (64 * w))
    (witness : A aX = b % c * 2 ^ (64 * w) % c)
    (one : A aOne = 2 ^ (64 * w) % c) (minus : A aMinusOne = c - 2 ^ (64 * w) % c)
    (exponent : A aExponent = mrE c) :
    (finishedState A c w (2 * w) (mrA c % 64)).2 = Spec.MillerRabin.round c b := by
  change (Word32.msqs c w (runValues A c w aMinusOne) (4 - sigOf (mrA c % 64)) 3
    (exponentState (runValues A c w) c w (2 * w) false (2 * w)) 3).2 = _
  rw [runValues_minus, sigOf_mod, exponentState_mrun (runValues A c w) c w (2 * w)
    (runValues_identity A c w) (2 * w) (Nat.le_refl _), runValues_minus, runValues_exp]
  have table : ∀ j < 16, runValues A c w (aTable + j) = Word32.tp c w (A aX) (A aOne) j :=
    fun j digit => runValues_power A c w digit
  rw [Word32.mrun_table_congr table c w (A aMinusOne) (A aExponent) (8 * (2 * w)) (8 * (2 * w)),
    show 8 * (2 * w) = 16 * w by omega, exponent]
  exact Word32.final_eq odd minimum fits witness one minus

end VG.Proof.MillerRabin.X86
