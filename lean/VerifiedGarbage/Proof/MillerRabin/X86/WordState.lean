module

public import VerifiedGarbage.Proof.MillerRabin.X86.WindowState

/-! # Eight windows consume one native exponent word from its top bits -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def wordState (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) : Nat → Nat × Bool
  | 0 => (A aY, F)
  | i + 1 => Word32.mwin c w (A aMinusOne) (fun d => A (aTable + d))
      ((x <<< (4 * i)) >>> 28).toNat (wordState A c w x F i)

def wordValues (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat) : Nat → Nat :=
  setAt A aY (wordState A c w x F i).1

def wordCounters (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat) :
    Nat → BitVec 32 :=
  setAt (setAt (setAt V sFlag (BitVec.ofNat 32 (wordState A c w x F i).2.toNat))
    sValue (x <<< (4 * i))) sWindows (BitVec.ofNat 32 (8 - i))

theorem wordState_lt (A : Nat → Nat) {c : Nat} (positive : 0 < c) (w : Nat) (x : BitVec 32) (F : Bool)
    (initial : A aY < c) : ∀ i, (wordState A c w x F i).1 < c
  | 0 => initial
  | _ + 1 => Word32.mm_lt positive

theorem wordValues_initial (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) :
    wordValues A c w x F 0 = A := setAt_same A aY

theorem wordCounters_initial (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool)
    (value : V sValue = x) (count : V sWindows = 8#32) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    wordCounters V A c w x F 0 = V := by
  change setAt (setAt (setAt V sFlag (BitVec.ofNat 32 F.toNat)) sValue (x <<< 0)) sWindows 8#32 = V
  rw [BitVec.shiftLeft_zero, ← flag, setAt_same, ← value, setAt_same, ← count, setAt_same]

theorem wordWindow_next (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat) :
    windowResult (wordCounters V A c w x F i) (wordValues A c w x F i) c w
      (wordState A c w x F i).2 = wordState A c w x F (i + 1) := by
  unfold windowResult wordValues
  rw [setAt_other _ _ (by decide : aMinusOne ≠ aY), setAt_self]
  have powers : (fun d => setAt A aY (wordState A c w x F i).1 (aTable + d)) =
      (fun d => A (aTable + d)) := by
    funext d
    exact setAt_other _ _ (by unfold aTable aY; omega)
  rw [powers]
  rfl

theorem wordValues_next (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat) :
    setAt (wordValues A c w x F i) aY
      (windowResult (wordCounters V A c w x F i) (wordValues A c w x F i) c w
        (wordState A c w x F i).2).1 = wordValues A c w x F (i + 1) := by
  rw [wordWindow_next, wordValues, setAt_twice]
  rfl

theorem wordCounters_next (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat)
    {d : Nat} (known : d ∈ windowFields) :
    windowCounters (wordCounters V A c w x F i) (wordValues A c w x F i) c w (8 - i)
      (wordState A c w x F i).2 d = wordCounters V A c w x F (i + 1) d := by
  change d ∈ [184, 208, 232, 240] at known
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl
  · change BitVec.ofNat 32 (windowResult (wordCounters V A c w x F i) (wordValues A c w x F i)
      c w (wordState A c w x F i).2).2.toNat = _
    rw [wordWindow_next]
    rfl
  · exact Word32.shl4_succ32 x i
  · rfl
  · change BitVec.ofNat 32 (8 - i - 1) = BitVec.ofNat 32 (8 - (i + 1))
    congr 1 <;> omega

end VG.Proof.MillerRabin.X86
