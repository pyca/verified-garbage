module

import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Proof.MillerRabin.ExponentWords32

/-! # A high-to-low native-word window is the corresponding exponent digit -/

@[expose] public section
namespace VG.Proof.MillerRabin

theorem exponentWindow_digit (E N j i : Nat) (word : j < N) (window : i < 8) :
    ((exponentWord E (N - 1 - j) <<< (4 * i)) >>> 28).toNat =
      E / 16 ^ (8 * N - 1 - (8 * j + i)) % 16 := by
  rw [Word32.shl_shr28 _ window, exponentWord, BitVec.toNat_ofNat,
    show 28 - 4 * i = 4 * (7 - i) by omega,
    Word32.digit_word E (N - 1 - j) (7 - i) (by omega)]
  rw [show 8 * (N - 1 - j) + (7 - i) = 8 * N - 1 - (8 * j + i) by omega]

end VG.Proof.MillerRabin
