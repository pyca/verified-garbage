module

public import VerifiedGarbage.Proof.MillerRabin.X86.SquareState
public import VerifiedGarbage.Proof.MillerRabin.X86.DataWindowControl
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath

/-! # Values through four squares, a complete table scan and one window product -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def windowFields : List Nat := [sFlag, sValue, sWords, sWindows]

def windowDigit (V : Nat → BitVec 32) : Nat := (V sValue >>> 28).toNat

def windowSquaresV (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat → BitVec 32 :=
  squareCounters (setAt (setAt V sThreshold 0#32) sSquares 4#32) A c w 0 4 F 4

def windowScanA (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat → Nat :=
  let sq := squareValues A c w 0 4 F 4
  setAt sq aX (sq (aTable + windowDigit V))

def windowProductA (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat → Nat :=
  let scan := windowScanA V A c w F
  setAt scan aY (Word32.mm c w (scan aY) (scan aX))

def windowOne (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Bool :=
  decide (windowProductA V A c w F aY = windowProductA V A c w F aOne)

def windowMinus (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Bool :=
  decide (windowProductA V A c w F aY = windowProductA V A c w F aMinusOne)

def windowEqV (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat → BitVec 32 :=
  setAt (setAt (windowSquaresV V A c w F) sEq1 (BitVec.ofNat 32 (windowOne V A c w F).toNat))
    sEq2 (BitVec.ofNat 32 (windowMinus V A c w F).toNat)

def windowResult (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) : Nat × Bool :=
  Word32.mwin c w (A aMinusOne) (fun d => A (aTable + d)) (windowDigit V) (A aY, F)

def windowCounters (V : Nat → BitVec 32) (A : Nat → Nat) (c w q : Nat) (F : Bool) : Nat → BitVec 32 :=
  setAt (setAt (setAt V sFlag (BitVec.ofNat 32 (windowResult V A c w F).2.toNat))
    sValue (V sValue <<< 4)) sWindows (BitVec.ofNat 32 (q - 1))

theorem windowSquares_digit (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) :
    windowSquaresV V A c w F sValue = V sValue := rfl

theorem windowScan_product (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool) :
    Word32.mm c w (windowScanA V A c w F aY) (windowScanA V A c w F aX) =
      (windowResult V A c w F).1 := by
  unfold windowScanA windowResult squareValues Word32.mwin
  rw [setAt_other _ _ (by decide : aY ≠ aX), setAt_self, setAt_self,
    setAt_other _ _ (by unfold aTable aY; omega : aTable + windowDigit V ≠ aY)]
  rfl

theorem windowProduct_value (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool)
    {j : Nat} (notX : j ≠ aX) :
    windowProductA V A c w F j = setAt A aY (windowResult V A c w F).1 j := by
  unfold windowProductA
  rw [windowScan_product]
  by_cases y : j = aY
  · subst j; rw [setAt_self, setAt_self]
  · rw [setAt_other _ _ y, windowScanA, setAt_other _ _ notX,
      squareValues, setAt_other _ _ y, setAt_other _ _ y]

theorem windowResult_flag (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (F : Bool)
    (one : A aTable = A aOne) :
    (if windowDigit V = 0 then (squareState A c w 0 4 F 4).2
      else windowOne V A c w F || windowMinus V A c w F) = (windowResult V A c w F).2 := by
  unfold windowOne windowMinus
  rw [windowProduct_value V A c w F (by decide : aY ≠ aX), setAt_self,
    windowProduct_value V A c w F (by decide : aOne ≠ aX),
    setAt_other _ _ (by decide : aOne ≠ aY),
    windowProduct_value V A c w F (by decide : aMinusOne ≠ aX),
    setAt_other _ _ (by decide : aMinusOne ≠ aY)]
  change (if windowDigit V = 0 then (squareState A c w 0 4 F 4).2 else
    decide ((windowResult V A c w F).1 = A aOne) ||
      decide ((windowResult V A c w F).1 = A aMinusOne)) = _
  rw [← one]
  rfl

theorem windowCounters_eq (V : Nat → BitVec 32) (A : Nat → Nat) (c w q : Nat) (F : Bool)
    (one : A aTable = A aOne) {d : Nat} (known : d ∈ windowFields) :
    windowSlots (windowEqV V A c w F) q (windowOne V A c w F) (windowMinus V A c w F)
      (squareState A c w 0 4 F 4).2 d = windowCounters V A c w q F d := by
  change d ∈ [184, 208, 232, 240] at known
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl
  · change BitVec.ofNat 32 (if windowDigit V = 0 then (squareState A c w 0 4 F 4).2 else
      windowOne V A c w F || windowMinus V A c w F).toNat = _
    rw [windowResult_flag V A c w F one]
    rfl
  · rfl
  · rfl
  · rfl

end VG.Proof.MillerRabin.X86
