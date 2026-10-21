module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State

/-! A candidate sees exactly the nonempty remaining suffix of the public entropy tape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

theorem SearchParams.source_addr (p : SearchParams) (used : Nat)
    (room : used + p.c.length ≤ p.c.bytes.length) :
    State.addr (p.c.tape + BitVec.ofNat 32 used) = off (State.addr p.c.tape) used := by
  have := p.c.tapeFits
  have := p.width_bounds.1
  exact VG.Arm.addr_add (by omega)

theorem SearchParams.source_fits (p : SearchParams) (used : Nat)
    (room : used + p.c.length ≤ p.c.bytes.length) :
    (p.c.tape + BitVec.ofNat 32 used).toNat + (p.c.bytes.length - used) ≤ 2 ^ 32 := by
  have width := p.width_bounds.1
  have tape := p.c.tapeFits
  have usedFit : used < 2 ^ 32 := by have := p.c.tapeCount; omega
  have startFit : p.c.tape.toNat + used < 2 ^ 32 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedFit, Nat.mod_eq_of_lt startFit]
  omega

theorem SearchParams.source_sub (p : SearchParams) (used : Nat)
    (room : used + p.c.length ≤ p.c.bytes.length) :
    (⟨State.addr (p.c.tape + BitVec.ofNat 32 used), p.c.bytes.length - used⟩ : Region).Sub
      ⟨State.addr p.c.tape, p.c.bytes.length⟩ := by
  rw [p.source_addr used room]
  exact Offset.sub_base _ (by omega)

theorem SearchLive.source_read {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (room : used + p.c.length ≤ p.c.bytes.length) :
    InRegions (s.rd ++ s.wr) (State.addr (p.c.tape + BitVec.ofNat 32 used)) (p.c.bytes.length - used) := by
  rw [p.source_addr used room]
  exact VG.CallLay.inRegions_sub h.buffers.tapeRead (by omega) (by have := p.c.tapeCount; omega)

theorem SearchLive.source_bytes {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (room : used + p.c.length ≤ p.c.bytes.length) :
    Spec.Rsa.bytesAt s.mem (State.addr (p.c.tape + BitVec.ofNat 32 used)) (p.c.bytes.length - used) = p.c.bytes.drop used := by
  rw [p.source_addr used room]
  have slice := VG.Proof.Dsa.bytesAt_slice s.mem (State.addr p.c.tape)
    (offset := used) (len := p.c.bytes.length - used) (by omega : used + (p.c.bytes.length - used) ≤ p.c.bytes.length)
  rw [h.buffers.tapeBytes] at slice
  have taken : (p.c.bytes.drop used).take (p.c.bytes.length - used) = p.c.bytes.drop used := by
    rw [← (List.length_drop (i := used) (l := p.c.bytes)), List.take_length]
  rw [taken] at slice
  exact slice.symm

end VG.Proof.Ffdh.Arm.ParameterSearch
