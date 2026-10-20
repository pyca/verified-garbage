module

public import VerifiedGarbage.Proof.MillerRabin.X86.WordState
public import VerifiedGarbage.Proof.MillerRabin.X86.WordStep

/-! # The outer public countdown consumes exponent words from high to low -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def exponentState (A : Nat → Nat) (c w N : Nat) (F : Bool) : Nat → Nat × Bool
  | 0 => (A aY, F)
  | i + 1 =>
    let st := exponentState A c w N F i
    wordState (setAt A aY st.1) c w (exponentWord (A aExponent) (N - 1 - i)) st.2 8

def exponentValues (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat) : Nat → Nat :=
  setAt A aY (exponentState A c w N F i).1

def exponentCounters (V : Nat → BitVec 32) (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat) :
    Nat → BitVec 32 :=
  setAt (setAt V sFlag (BitVec.ofNat 32 (exponentState A c w N F i).2.toNat)) sWords (BitVec.ofNat 32 (N - i))

theorem exponentState_lt (A : Nat → Nat) {c : Nat} (positive : 0 < c) (w N : Nat) (F : Bool)
    (initial : A aY < c) : ∀ i, (exponentState A c w N F i).1 < c
  | 0 => initial
  | i + 1 => wordState_lt _ positive _ _ _ (by
      rw [setAt_self]
      exact exponentState_lt A positive w N F initial i) 8

theorem exponentValues_initial (A : Nat → Nat) (c w N : Nat) (F : Bool) :
    exponentValues A c w N F 0 = A := setAt_same A aY

theorem exponentCounters_initial (V : Nat → BitVec 32) (A : Nat → Nat) (c w N : Nat) (F : Bool)
    (count : V sWords = BitVec.ofNat 32 N) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    exponentCounters V A c w N F 0 = V := by
  change setAt (setAt V sFlag (BitVec.ofNat 32 F.toNat)) sWords (BitVec.ofNat 32 N) = V
  rw [← flag, setAt_same, ← count, setAt_same]

theorem exponentWord_next (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat) :
    wordState (exponentValues A c w N F i) c w
      (exponentWord (exponentValues A c w N F i aExponent) (N - i - 1))
      (exponentState A c w N F i).2 8 = exponentState A c w N F (i + 1) := by
  unfold exponentValues
  rw [setAt_other _ _ (by decide : aExponent ≠ aY), Nat.sub_right_comm]
  rfl

theorem exponentValues_next (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat) :
    wordValues (exponentValues A c w N F i) c w
      (exponentWord (exponentValues A c w N F i aExponent) (N - i - 1))
      (exponentState A c w N F i).2 8 = exponentValues A c w N F (i + 1) := by
  unfold wordValues
  rw [exponentWord_next, exponentValues, setAt_twice]
  rfl

theorem exponentCounters_next (V : Nat → BitVec 32) (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat)
    {d : Nat} (known : d ∈ wordFields) :
    wordEndSlots (exponentCounters V A c w N F i) (exponentValues A c w N F i) c w
      (exponentWord (exponentValues A c w N F i aExponent) (N - i - 1))
      (exponentState A c w N F i).2 (N - i) d = exponentCounters V A c w N F (i + 1) d := by
  change d ∈ [184, 232] at known
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl
  · change BitVec.ofNat 32 (wordState (exponentValues A c w N F i) c w
      (exponentWord (exponentValues A c w N F i aExponent) (N - i - 1))
      (exponentState A c w N F i).2 8).2.toNat = _
    rw [exponentWord_next]
    rfl
  · change BitVec.ofNat 32 (N - i - 1) = BitVec.ofNat 32 (N - (i + 1))
    congr 1 <;> omega

end VG.Proof.MillerRabin.X86
