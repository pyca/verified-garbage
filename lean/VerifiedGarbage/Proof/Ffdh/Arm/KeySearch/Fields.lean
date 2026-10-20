module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-! The controller's stable fields, indexed independently of their values. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm

def headerIndices : List Nat := [0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15]

def KeyPublic.field (p : KeyPublic sampling) (used keys scalars j : Nat) : BitVec 32 :=
  match j with
  | 0 => BitVec.ofNat 32 keys
  | 1 => BitVec.ofNat 32 scalars
  | 2 => BitVec.ofNat 32 p.len
  | 5 => p.xp
  | 6 => p.yp
  | 7 => p.dp
  | 8 => BitVec.ofNat 32 p.dlen
  | 9 => p.rp + BitVec.ofNat 32 used
  | 10 => BitVec.ofNat 32 (p.randLen - used)
  | 11 => BitVec.ofNat 32 used
  | 12 => p.scratch
  | 13 => BitVec.ofNat 32 p.capacity
  | 15 => p.up
  | _ => 0

theorem KeyPublic.headers_map (p : KeyPublic sampling) (used keys scalars : Nat) :
    p.headers used keys scalars = headerIndices.map (fun j => (j, p.field used keys scalars j)) := rfl

theorem slots_fields (m : Mem) (base : BitVec 32) (p : KeyPublic sampling) (used keys scalars : Nat) :
    Slots m base (p.headers used keys scalars) ↔
      ∀ j ∈ headerIndices, lowWord m base j = p.field used keys scalars j := by
  rw [KeyPublic.headers_map]
  simp only [Slots, List.forall_mem_map]

theorem KeyLive.field {p : KeyPublic sampling} {original s : State} {used keys scalars j : Nat}
    (h : KeyLive p original used keys scalars s) (member : j ∈ headerIndices) :
    lowWord s.mem p.control j = p.field used keys scalars j :=
  (slots_fields _ _ _ _ _ _).mp h.headers j member

theorem headerIndices_bound {j : Nat} (member : j ∈ headerIndices) : j < 16 := by
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

end VG.Proof.Ffdh.Arm.KeySearch
