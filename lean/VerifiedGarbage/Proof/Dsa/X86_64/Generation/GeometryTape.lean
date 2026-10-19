module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Geometry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
import VerifiedGarbage.Proof.Framework.Omega

/-! # Immutable entropy tapes are disjoint from every mutable generation area -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure GenerationTape (p : GenerationGeometry) where
  ptr : Addr
  bytes : List Byte
  bound : ptr.toNat + bytes.length ≤ 2 ^ 64
  size : bytes.length < 2 ^ 64
  arena : (⟨ptr, bytes.length⟩ : Region).Disjoint ⟨p.B, usedBytes p.pLen⟩
  frame : (⟨ptr, bytes.length⟩ : Region).Disjoint ⟨p.F, frameBytes⟩
  stack : (⟨ptr, bytes.length⟩ : Region).Disjoint (below p.F 128)

theorem GenerationTape.part {p : GenerationGeometry} (tape : GenerationTape p) {d n : Nat}
    (h : d + n ≤ usedBytes p.pLen) : (⟨tape.ptr, tape.bytes.length⟩ : Region).Disjoint (p.part d n) :=
  tape.arena.sub_right (p.part_sub h)

def GenerationTape.slice {p : GenerationGeometry} (tape : GenerationTape p) (used len : Nat)
    (room : used + len ≤ tape.bytes.length) : GenerationTape p where
  ptr := off tape.ptr used
  bytes := (tape.bytes.drop used).take len
  bound := by
    have hb := tape.bound
    have hl : ((tape.bytes.drop used).take len).length = len := by
      simp only [List.length_take, List.length_drop]; omega
    rw [hl]
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [hb, room, tape.size]
  size := by simp only [List.length_take, List.length_drop]; omega_using [room, tape.size]
  arena := tape.arena.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))
  frame := tape.frame.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))
  stack := tape.stack.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))

theorem GenerationTape.source {p : GenerationGeometry} (tape : GenerationTape p) {s : State}
    {d n : Nat} (hd : d + n ≤ usedBytes p.pLen)
    (hr : ∀ i < tape.bytes.length, InRegions (s.rd ++ s.wr) (off tape.ptr i) 1)
    (hv : ∀ i (hi : i < tape.bytes.length), s.mem (off tape.ptr i) = tape.bytes[i]'hi) :
    Src s (off p.B d) n tape.ptr tape.bytes :=
  ⟨hr, hv, fun i hi => out_scr (tape.part hd)
    (Offset.contains_base _ (by omega) (by omega_using [hi, tape.size]))⟩

end VG.Proof.Dsa.X86_64.Generation
