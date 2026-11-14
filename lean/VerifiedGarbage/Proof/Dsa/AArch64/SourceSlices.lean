module
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup

import VerifiedGarbage.Proof.Framework.AddrArith
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Memory-safe component and digest slices of external DSA inputs -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem source_slice {s : State} {B p : Addr} {Z offset len : Nat} {bs : List Byte}
    (h : Src s B Z p bs) (hl : offset + len ≤ bs.length) :
    Src s B Z (p + BitVec.ofNat 64 offset) ((bs.drop offset).take len) := by
  have hlen : ((bs.drop offset).take len).length = len := by
    simp only [List.length_take, List.length_drop]
    omega_using [hl]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    rw [Offset.add_add]
    exact h.rd _ (by omega_using [hl, hi])
  · intro i hi
    rw [Offset.add_add, h.val _ (by omega_using [hl, hlen, hi])]
    simp only [List.getElem_take, List.getElem_drop]
  · intro i hi
    rw [hlen] at hi
    rw [Offset.add_add]
    exact h.out _ (by omega_using [hl, hi])

theorem source_take {s : State} {B p : Addr} {Z n : Nat} {bs : List Byte}
    (h : Src s B Z p bs) : Src s B Z p (bs.take n) := by
  have hlen : (bs.take n).length ≤ bs.length := by simp only [List.length_take]; omega_using []
  exact ⟨fun i hi => h.rd i (by omega_using [hlen, hi]),
    fun i hi => (h.val i (by omega_using [hlen, hi])).trans List.getElem_take.symm,
    fun i hi => h.out i (by omega_using [hlen, hi])⟩

structure PackedComponents (pLen qLen : Nat) where
  p : List Byte
  q : List Byte
  g : List Byte
  y : List Byte
  x : List Byte
  pLength : p.length = pLen
  qLength : q.length = qLen
  gLength : g.length = pLen
  yLength : y.length = pLen

/-- Slice lengths are independent of leading-zero encodings. -/
theorem component_length {bs : List Byte} {offset len : Nat} (h : offset + len ≤ bs.length) :
    ((bs.drop offset).take len).length = len := by
  simp only [List.length_take, List.length_drop]
  omega_using [h]

def packedComponents (pLen qLen : Nat) (key : List Byte) (hlen : 3 * pLen + qLen ≤ key.length) :
    PackedComponents pLen qLen where
  p := key.take pLen
  q := (key.drop pLen).take qLen
  g := (key.drop (pLen + qLen)).take pLen
  y := (key.drop (2 * pLen + qLen)).take pLen
  x := (key.drop (3 * pLen + qLen)).take qLen
  pLength := by simp only [List.length_take]; omega_using [hlen]
  qLength := component_length (by omega_using [hlen])
  gLength := component_length (by omega_using [hlen])
  yLength := component_length (by omega_using [hlen])

end VG.Proof.Dsa.AArch64
