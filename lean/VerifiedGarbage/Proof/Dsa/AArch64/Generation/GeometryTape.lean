module

public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaOaep.AArch64
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Impl.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
/-! # Immutable entropy tapes are disjoint from every mutable generation area -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Geometry.lean`, which only this module imported.
section

/-! # Shared concrete arena geometry for composing parameter-generation phases -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure GenerationGeometry where
  B : Addr
  F : Addr
  pLen : Nat
  qLen : Nat
  lengths : Spec.Dsa.generationLengthsValid pLen qLen
  arenaBound : B.toNat + usedBytes pLen ≤ 2 ^ 64
  frameBound : F.toNat + frameBytes ≤ 2 ^ 64
  stackSize : 272 ≤ F.toNat
  frameArena : (⟨F, frameBytes⟩ : Region).Disjoint ⟨B, usedBytes pLen⟩
  stackArena : (below F 272).Disjoint ⟨B, usedBytes pLen⟩
  /-- The stack the generator stage's contract asks for below the frame. -/
  callSize : 288 ≤ F.toNat
  callArena : (below F 288).Disjoint ⟨B, usedBytes pLen⟩

def GenerationGeometry.part (p : GenerationGeometry) (offset len : Nat) : Region := ⟨VG.Proof.Bignum.off p.B offset, len⟩
def GenerationGeometry.hash (p : GenerationGeometry) : Addr := VG.Proof.Bignum.off p.B VG.Impl.Dsa.Generation.Layout.hash

theorem GenerationGeometry.width (p : GenerationGeometry) :
    p.pLen = 128 ∨ p.pLen = 256 ∨ p.pLen = 384 := by
  rcases p.lengths with h | h | h <;> simp [h.1]

theorem GenerationGeometry.qWidth (p : GenerationGeometry) : p.qLen = 20 ∨ p.qLen = 32 := by
  rcases p.lengths with h | h | h <;> simp [h.2]

theorem GenerationGeometry.part_sub (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    Region.Sub (p.part d n) ⟨p.B, usedBytes p.pLen⟩ := Offset.sub_base p.B h

theorem GenerationGeometry.part_bound (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    (VG.Proof.Bignum.off p.B d).toNat + n ≤ 2 ^ 64 := by
  have hb := p.arenaBound
  have hd : d < 2 ^ 64 := by
    have ht : usedBytes p.pLen < 2 ^ 64 := by rcases p.width with hh | hh | hh <;> rw [hh] <;> decide
    omega
  simp only [VG.Proof.Bignum.off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  omega

theorem GenerationGeometry.frame_part (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    (⟨p.F, frameBytes⟩ : Region).Disjoint (p.part d n) := p.frameArena.sub_right (p.part_sub h)

theorem GenerationGeometry.stack_part (p : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes p.pLen) :
    (below p.F 272).Disjoint (p.part d n) := p.stackArena.sub_right (p.part_sub h)

theorem GenerationGeometry.parts_disjoint (p : GenerationGeometry) {d n e k : Nat}
    (hd : d + n ≤ usedBytes p.pLen) (he : e + k ≤ usedBytes p.pLen)
    (h : d + n ≤ e ∨ e + k ≤ d) : (p.part d n).Disjoint (p.part e k) := by
  have hb := p.arenaBound
  exact Offset.disjoint p.B h (by omega) (by omega)

theorem GenerationGeometry.frame_below (p : GenerationGeometry) :
    (⟨p.F, frameBytes⟩ : Region).Disjoint (below p.F 272) :=
  Offset.base_disjoint_below p.F (by decide)

theorem GenerationGeometry.frame_headers (p : GenerationGeometry) :
    ∀ k < 34, ∀ j < 32, Mem.Sep (VG.Proof.Bignum.off p.F (8 * k)) 8
      (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B arithmetic) (8 * j)) 8 := by
  intro k hk j hj
  apply (p.frame_part (d := arithmetic) (n := arithmeticBytes) (by
    rcases p.width with hh | hh | hh <;> rw [hh] <;> decide)).sep
  · exact Offset.contains_base _ (by unfold frameBytes; omega) (by omega)
  · exact Offset.contains_base _ (by unfold arithmeticBytes; omega) (by omega)

theorem GenerationGeometry.frame_outside (p : GenerationGeometry) :
    ∀ k < 34, ∀ i < 8, arithmeticBytes ≤ ofs (VG.Proof.Bignum.off p.B arithmetic) (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.F (8 * k)) i) := by
  intro k hk i hi
  rw [VG.Proof.Bignum.off_off]
  exact out_scr (p.frame_part (d := arithmetic) (n := arithmeticBytes) (by
    rcases p.width with hh | hh | hh <;> rw [hh] <;> decide))
    (Offset.contains_base _ (by unfold frameBytes; omega) (by omega))

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure GenerationTape (p : GenerationGeometry) where
  ptr : Addr
  bytes : List Byte
  bound : ptr.toNat + bytes.length ≤ 2 ^ 64
  size : bytes.length < 2 ^ 64
  arena : (⟨ptr, bytes.length⟩ : Region).Disjoint ⟨p.B, usedBytes p.pLen⟩
  frame : (⟨ptr, bytes.length⟩ : Region).Disjoint ⟨p.F, frameBytes⟩
  stack : (⟨ptr, bytes.length⟩ : Region).Disjoint (below p.F 272)
  callStack : (⟨ptr, bytes.length⟩ : Region).Disjoint (below p.F 288)

theorem GenerationTape.part {p : GenerationGeometry} (tape : GenerationTape p) {d n : Nat}
    (h : d + n ≤ usedBytes p.pLen) : (⟨tape.ptr, tape.bytes.length⟩ : Region).Disjoint (p.part d n) :=
  tape.arena.sub_right (p.part_sub h)

def GenerationTape.slice {p : GenerationGeometry} (tape : GenerationTape p) (used len : Nat)
    (room : used + len ≤ tape.bytes.length) : GenerationTape p where
  ptr := VG.Proof.Bignum.off tape.ptr used
  bytes := (tape.bytes.drop used).take len
  bound := by
    have hb := tape.bound
    have hl : ((tape.bytes.drop used).take len).length = len := by
      simp only [List.length_take, List.length_drop]; omega
    rw [hl]
    simp only [VG.Proof.Bignum.off, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [hb, room, tape.size]
  size := by simp only [List.length_take, List.length_drop]; omega_using [room, tape.size]
  arena := tape.arena.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))
  frame := tape.frame.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))
  stack := tape.stack.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))
  callStack := tape.callStack.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))

theorem GenerationTape.source {p : GenerationGeometry} (tape : GenerationTape p) {s : State}
    {d n : Nat} (hd : d + n ≤ usedBytes p.pLen)
    (hr : ∀ i < tape.bytes.length, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off tape.ptr i) 1)
    (hv : ∀ i (hi : i < tape.bytes.length), s.mem (VG.Proof.Bignum.off tape.ptr i) = tape.bytes[i]'hi) :
    Src s (VG.Proof.Bignum.off p.B d) n tape.ptr tape.bytes :=
  ⟨hr, hv, fun i hi => out_scr (tape.part hd)
    (Offset.contains_base _ (by omega) (by omega_using [hi, tape.size]))⟩

end VG.Proof.Dsa.AArch64.Generation
