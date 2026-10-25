module

import VerifiedGarbage.Proof.Ffdh.Arm.StoreSlot
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! The pointers into the packed domain stay in the local frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem domainPointers_store (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (source : s.gpr .r4 = p.domain) (count : s.gpr .r6 = BitVec.ofNat 32 p.k)
    (stackBase : s.gpr .r12 = s.sp) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.domainPointers) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr s.sp) 56) p.g).writeW (off (State.addr s.sp) 60) p.q ∧ Rest [.r3] s t := by
  have addr (d : Nat) (hd : d ≤ 68) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have w56 := h.locals.space.write (off := 56) (by decide)
  have w60 := h.locals.space.write (off := 60) (by decide)
  have q : p.g + BitVec.ofNat 32 p.k = p.q := by
    change (p.domain + BitVec.ofNat 32 p.k) + BitVec.ofNat 32 p.k = p.domain + BitVec.ofNat 32 (2 * p.k)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show p.k + p.k = 2 * p.k by omega]
  refine withRest_all [.r3] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.domainPointers VG.Impl.Ffdh.Arm.Domain.st
  ffrun [source, count, stackBase, addr 56 (by decide), addr 60 (by decide), w56, w60, off, Inputs.g, Inputs.q,
    BitVec.add_assoc, ← BitVec.ofNat_add, show p.k + p.k = 2 * p.k by omega]

theorem domainPointers_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (source : s.gpr .r4 = p.domain) (count : s.gpr .r6 = BitVec.ofNat 32 p.k)
    (stackBase : s.gpr .r12 = s.sp) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.domainPointers) s fun t => Context p (60 :: 56 :: slots) t ∧
      Frame [⟨off (State.addr s.sp) 56, 4⟩, ⟨off (State.addr s.sp) 60, 4⟩] s.mem t.mem ∧ Rest [.r3] s t := by
  refine WP.mono (domainPointers_store s h source count stackBase) ?_
  rintro t ⟨mem, rest⟩
  let mid := putMem s (s.mem.writeW (off (State.addr s.sp) 56) p.g)
  have midRest : Rest [] s mid := ⟨by intro r _; rfl, rfl, rfl, rfl⟩
  have midContext := h.store_slot stable 56 (by decide) (by decide) (t := mid) rfl midRest h.ptr
  have midStable : stableSlots (56 :: slots) = true := by
    change (true && stableSlots slots) = true
    rw [Bool.true_and, stable]
  have lastRest : Rest [.r3] mid t := ⟨rest.gpr, rest.rd, rest.wr, rest.sp⟩
  have context := midContext.store_slot midStable 60 (by decide) (by decide) mem lastRest
    ((rest.gpr .r0 (by simp)).trans h.ptr)
  refine ⟨context, ?_, rest⟩
  rw [mem]
  exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
    (by simp) _ (Region.contains_self _ _)

end VG.Proof.Ffdh.Arm
