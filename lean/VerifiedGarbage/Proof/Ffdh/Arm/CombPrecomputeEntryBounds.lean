module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Each packed table entry is a disjoint slice of the context output. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Mont

theorem entry_geometry {p : Inputs} {sp : BitVec 32} {s : State} {digit : Nat}
    (h : Memory p sp s) (hd : digit < 32) :
    let src := p.output + BitVec.ofNat 32 (entryOffset p digit)
    State.addr src = off (State.addr p.output) (entryOffset p digit) ∧
      src.toNat + 8*p.w ≤ 2^32 ∧
      InRegions (s.rd++s.wr) (State.addr src) (8*p.w) ∧
      Region.Disjoint ⟨State.addr p.base,8*p.len⟩ ⟨State.addr src,8*p.w⟩ := by
  dsimp only
  have bound := entry_bound p hd
  have hw := p.width.1
  have small : p.output.toNat + entryOffset p digit < 2^32 := by have := h.output.fits; omega
  have address : State.addr (p.output + BitVec.ofNat 32 (entryOffset p digit)) =
      off (State.addr p.output) (entryOffset p digit) := addr_add small
  have fit : (p.output + BitVec.ofNat 32 (entryOffset p digit)).toNat + 8*p.w ≤ 2^32 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : entryOffset p digit < 2^32),Nat.mod_eq_of_lt small]
    have := h.output.fits
    omega
  have write := CallLay.inRegions_sub h.output.writable bound
    (by have := h.output.fits; omega : bytes p < 2^64)
  obtain ⟨r,hr,contains⟩ := write
  refine ⟨address,fit,?_,?_⟩
  · rw [address]
    exact ⟨r,List.mem_append_right _ hr,contains⟩
  · rw [address]
    exact h.workspaceSeparate.sub_right (entry_sub p hd)

end VG.Proof.Ffdh.Arm.CombBuilder
