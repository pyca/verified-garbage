module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! A nested attempt receives exactly the next public-width slice of entropy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont

abbrev rTape (p : KeyPublic) (used : Nat) : Region :=
  ⟨State.addr (p.rp + BitVec.ofNat 32 used), p.len⟩

theorem KeyInput.tape_addr {p : KeyPublic} {s : State} {used : Nat}
    (h : KeyInput p s) (room : used + p.len ≤ p.randLen) :
    State.addr (p.rp + BitVec.ofNat 32 used) = off (State.addr p.rp) used :=
  VG.Arm.addr_add (by have := h.bounds.randomFit; have := h.bounds.minLength; omega)

theorem KeyInput.tape_sub {p : KeyPublic} {s : State} {used : Nat}
    (h : KeyInput p s) (room : used + p.len ≤ p.randLen) : (rTape p used).Sub (rRandom p) := by
  change (⟨State.addr (p.rp + BitVec.ofNat 32 used), p.len⟩ : Region).Sub _
  rw [h.tape_addr room]
  exact Offset.sub_base _ room

theorem KeyInput.tape_fits {p : KeyPublic} {s : State} {used : Nat}
    (h : KeyInput p s) (room : used + p.len ≤ p.randLen) :
    (p.rp + BitVec.ofNat 32 used).toNat + p.len ≤ 2 ^ 32 := by
  have fits := h.bounds.randomFit
  have positive := h.bounds.minLength
  have usedFits : used < 2 ^ 32 := by omega
  have pointerFits : p.rp.toNat + used < 2 ^ 32 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedFits, Nat.mod_eq_of_lt pointerFits]
  omega

theorem KeyLive.tape_bytes {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen) :
    Spec.Rsa.bytesAt s.mem (State.addr (p.rp + BitVec.ofNat 32 used)) p.len =
      ((keyRand p original).drop used).take p.len := by
  have slice : ((Spec.Rsa.bytesAt s.mem (State.addr p.rp) p.randLen).drop used).take p.len =
      Spec.Rsa.bytesAt s.mem (off (State.addr p.rp) used) p.len :=
    VG.Proof.MlKem.bytesAt_slice s.mem (State.addr p.rp) room
  rw [h.input.tape_addr room, ← slice, h.random]
  rfl

end VG.Proof.Ffdh.Arm.KeySearch
