module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Proof.MillerRabin.X86.DataSquareControl

/-! # Canonical values while a public number of squarings is counted down -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def squareState (A : Nat → Nat) (c w r q : Nat) (F : Bool) (i : Nat) : Nat × Bool :=
  Word32.msqs c w (A aMinusOne) r q (A aY, F) i

def squareValues (A : Nat → Nat) (c w r q : Nat) (F : Bool) (i : Nat) : Nat → Nat :=
  setAt A aY (squareState A c w r q F i).1

def squareCounters (V : Nat → BitVec 32) (A : Nat → Nat) (c w r q : Nat) (F : Bool) (i : Nat) :
    Nat → BitVec 32 :=
  setAt (setAt V sSquares (BitVec.ofNat 32 (q - i))) sFlag
    (BitVec.ofNat 32 (squareState A c w r q F i).2.toNat)

theorem squareState_lt (A : Nat → Nat) {c : Nat} (positive : 0 < c) (w r q : Nat) (F : Bool)
    (initial : A aY < c) : ∀ i, (squareState A c w r q F i).1 < c
  | 0 => initial
  | _ + 1 => Word32.mm_lt positive

theorem squareValues_initial (A : Nat → Nat) (c w r q : Nat) (F : Bool) :
    squareValues A c w r q F 0 = A := setAt_same A aY

theorem squareCounters_initial (V : Nat → BitVec 32) (A : Nat → Nat) (c w r q : Nat) (F : Bool)
    (count : V sSquares = BitVec.ofNat 32 q) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    squareCounters V A c w r q F 0 = V := by
  change setAt (setAt V sSquares (BitVec.ofNat 32 q)) sFlag (BitVec.ofNat 32 F.toNat) = V
  rw [← count, setAt_same, ← flag, setAt_same]

theorem squareValues_next (A : Nat → Nat) (c w r q : Nat) (F : Bool) (i : Nat) :
    setAt (squareValues A c w r q F i) aY
      (Word32.mm c w (squareValues A c w r q F i aY) (squareValues A c w r q F i aY)) =
      squareValues A c w r q F (i + 1) := by
  unfold squareValues
  rw [setAt_self, setAt_twice]
  rfl

theorem squareCounters_next (V : Nat → BitVec 32) (A : Nat → Nat) (c w r q : Nat) (F : Bool)
    {i d : Nat} (notEq : d ≠ sEq2) :
    let values := squareValues A c w r q F i
    let E := decide (Word32.mm c w (values aY) (values aY) = values aMinusOne)
    squareSlots (setAt (squareCounters V A c w r q F i) sEq2 (BitVec.ofNat 32 E.toNat))
      (q - i) r E (squareState A c w r q F i).2 d = squareCounters V A c w r q F (i + 1) d := by
  dsimp only
  by_cases flag : d = sFlag
  · subst d
    change BitVec.ofNat 32 _ = BitVec.ofNat 32 _
    congr 1
    change ((squareState A c w r q F i).2 ||
      (decide (Word32.mm c w (squareState A c w r q F i).1 (squareState A c w r q F i).1 = A aMinusOne) &&
        decide (r < q - i))).toNat = _
    change _ = ((squareState A c w r q F i).2 ||
      (decide (r < q - i) && decide (Word32.mm c w (squareState A c w r q F i).1
        (squareState A c w r q F i).1 = A aMinusOne))).toNat
    rw [Bool.and_comm]
  · by_cases count : d = sSquares
    · subst d
      change BitVec.ofNat 32 (q - i - 1) = BitVec.ofNat 32 (q - (i + 1))
      congr 1 <;> omega
    · simp only [squareSlots, squareCounters, setAt_other _ _ flag, setAt_other _ _ count,
        setAt_other _ _ notEq]

end VG.Proof.MillerRabin.X86
