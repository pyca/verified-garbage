module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.StoreSlot
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Arm.Isa

/-! Set up native entropy cutting and retain the significant scalar pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyScalarArgs_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h20 : 20 ∈ slots) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs) s fun t =>
      (t.gpr .r0 = p.privateValue ∧ t.gpr .r1 = p.entropy ∧ t.gpr .lr = BitVec.ofNat 32 p.scalarLead ∧
        t.gpr .r2 = 0 ∧ t.mem = s.mem.writeW (off (State.addr s.sp) 16) p.scalarStart) ∧
      Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have r20 := h.locals.read (d := 20) (by decide)
  have r32 := h.locals.read (d := 32) (by decide)
  have r40 := h.locals.read (d := 40) (by decide)
  have r48 := h.locals.read (d := 48) (by decide)
  have w16 := h.locals.space.write (off := 16) (by decide)
  have leadCount : BitVec.ofNat 32 p.k - BitVec.ofNat 32 p.scalarWidth = BitVec.ofNat 32 p.scalarLead := by
    rw [Offset.ofNat_sub_ofNat p.scalarWidthBounds.2]
    apply congrArg (BitVec.ofNat 32)
    have := p.scalarLeadBound
    unfold Inputs.scalarWidth
    omega
  refine withRest [.r0, .r1, .r2, .r3, .r12, .lr] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs : Prog isa)).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs VG.Impl.Ffdh.Arm.Domain.st
  ffrun [addr 20 (by decide), addr 32 (by decide), addr 40 (by decide), addr 48 (by decide),
    addr 16 (by decide), r20, r32, r40, r48, w16, h.saved 20 h20, h.saved 32 h32,
    h.saved 40 h40, h.saved 48 h48, Inputs.slotValue, Inputs.scalarStart, leadCount, BitVec.add_zero, off]

theorem keyScalarArgs_retained (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h20 : 20 ∈ slots) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs) s fun t =>
      ArgumentMemory p (16 :: slots) t ∧ t.gpr .r0 = p.privateValue ∧ t.gpr .r1 = p.entropy ∧
      t.gpr .lr = BitVec.ofNat 32 p.scalarLead ∧ t.gpr .r2 = 0 ∧
      Frame [⟨off (State.addr s.sp) 16, 4⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  refine WP.mono (keyScalarArgs_ok s h h20 h32 h40 h48) ?_
  rintro t ⟨⟨dst, src, count, zero, mem⟩, rest⟩
  have context := h.toArgumentMemory.store_slot stable 16 (by decide) (by decide) mem rest
  refine ⟨context, dst, src, count, zero, ?_, rest⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)

end VG.Proof.Ffdh.Arm
