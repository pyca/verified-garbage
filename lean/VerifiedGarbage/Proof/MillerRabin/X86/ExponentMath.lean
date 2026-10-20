module

public import VerifiedGarbage.Proof.MillerRabin.X86.ExponentState
import VerifiedGarbage.Proof.MillerRabin.NativeDigits32

/-! # The native-word execution order is the shared mathematical window run -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

theorem wordState_mrun (A : Nat → Nat) (c w E N j : Nat) (F : Bool)
    (word : j < N)
    (initial : (A aY, F) = Word32.mrun c w (A aMinusOne) (fun d => A (aTable + d)) E (8 * N) (8 * j)) :
    ∀ i, i ≤ 8 → wordState A c w (exponentWord E (N - 1 - j)) F i =
      Word32.mrun c w (A aMinusOne) (fun d => A (aTable + d)) E (8 * N) (8 * j + i)
  | 0, _ => by simpa only [wordState, Nat.add_zero] using initial
  | i + 1, bound => by
    rw [wordState, wordState_mrun A c w E N j F word initial i (by omega),
      show 8 * j + (i + 1) = (8 * j + i) + 1 by omega, Word32.mrun,
      exponentWindow_digit E N j i word (by omega)]

theorem powerView_setY (A : Nat → Nat) (y : Nat) :
    (fun d => setAt A aY y (aTable + d)) = (fun d => A (aTable + d)) := by
  funext d
  exact setAt_other _ _ (by unfold aTable aY; omega)

theorem exponentState_mrun (A : Nat → Nat) (c w N : Nat) (one : A aY = A aTable) :
    ∀ j, j ≤ N → exponentState A c w N false j =
      Word32.mrun c w (A aMinusOne) (fun d => A (aTable + d)) (A aExponent) (8 * N) (8 * j)
  | 0, _ => by
    change (A aY, false) = (A (aTable + 0), false)
    rw [Nat.add_zero, one]
  | j + 1, bound => by
    have ih := exponentState_mrun A c w N one j (by omega)
    let st := exponentState A c w N false j
    let nextA := setAt A aY st.1
    have start : (nextA aY, st.2) =
        Word32.mrun c w (nextA aMinusOne) (fun d => nextA (aTable + d)) (A aExponent) (8 * N) (8 * j) := by
      change (setAt A aY st.1 aY, st.2) = _
      rw [setAt_self]
      change st = Word32.mrun c w (setAt A aY st.1 aMinusOne)
        (fun d => setAt A aY st.1 (aTable + d)) (A aExponent) (8 * N) (8 * j)
      rw [setAt_other _ _ (by decide : aMinusOne ≠ aY), powerView_setY]
      exact ih
    have result := wordState_mrun nextA c w (A aExponent) N j st.2 (by omega) start 8 (by decide)
    change wordState nextA c w (exponentWord (A aExponent) (N - 1 - j)) st.2 8 = _
    rw [result]
    change Word32.mrun c w (setAt A aY st.1 aMinusOne) (fun d => setAt A aY st.1 (aTable + d))
      (A aExponent) (8 * N) (8 * j + 8) = _
    rw [setAt_other _ _ (by decide : aMinusOne ≠ aY), powerView_setY,
      show 8 * j + 8 = 8 * (j + 1) by omega]

end VG.Proof.MillerRabin.X86
