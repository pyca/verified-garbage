module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Memory-safe component and digest slices of external DSA inputs -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem source_slice {s : State} {B p : Addr} {Z offset len : Nat} {bs : List Byte}
    (h : Src s B Z p bs) (hl : offset + len ≤ bs.length) :
    Src s B Z (p + BitVec.ofNat 64 offset) ((bs.drop offset).take len) := by
  have hlen : ((bs.drop offset).take len).length = len := by
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    rw [Offset.add_add]
    exact h.rd _ (by omega)
  · intro i hi
    rw [Offset.add_add, h.val _ (by omega)]
    simp only [List.getElem_take, List.getElem_drop]
  · intro i hi
    rw [hlen] at hi
    rw [Offset.add_add]
    exact h.out _ (by omega)

theorem source_take {s : State} {B p : Addr} {Z n : Nat} {bs : List Byte}
    (h : Src s B Z p bs) : Src s B Z p (bs.take n) := by
  have hlen : (bs.take n).length ≤ bs.length := by simp only [List.length_take]; omega
  exact ⟨fun i hi => h.rd i (by omega),
    fun i hi => (h.val i (by omega)).trans List.getElem_take.symm,
    fun i hi => h.out i (by omega)⟩

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
  omega

def packedComponents (pLen qLen : Nat) (key : List Byte) (hlen : 3 * pLen + qLen ≤ key.length) :
    PackedComponents pLen qLen where
  p := key.take pLen
  q := (key.drop pLen).take qLen
  g := (key.drop (pLen + qLen)).take pLen
  y := (key.drop (2 * pLen + qLen)).take pLen
  x := (key.drop (3 * pLen + qLen)).take qLen
  pLength := by simp only [List.length_take]; omega
  qLength := component_length (by omega)
  gLength := component_length (by omega)
  yLength := component_length (by omega)

end VG.Proof.Dsa.X86_64
