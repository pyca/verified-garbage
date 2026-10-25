module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
import VerifiedGarbage.Proof.Ffdh.Arm.StoreSlot
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Arm.Isa

/-! Store the public significant width and first-byte mask in native local slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyBoundSave_store (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (count : s.gpr .r6 = BitVec.ofNat 32 p.scalarWidth) (mask : s.gpr .r3 = p.scalarMask) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr s.sp) 20) (BitVec.ofNat 32 p.scalarWidth)).writeW
        (off (State.addr s.sp) 68) p.scalarMask ∧ Rest [.r12] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have w20 := h.locals.space.write (off := 20) (by decide)
  have w68 := h.locals.space.write (off := 68) (by decide)
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave VG.Impl.Ffdh.Arm.Domain.st
  ffrun [count, mask, addr 20 (by decide), addr 68 (by decide), w20, w68, BitVec.add_zero, off]

theorem keyBoundSave_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (count : s.gpr .r6 = BitVec.ofNat 32 p.scalarWidth) (mask : s.gpr .r3 = p.scalarMask) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave) s fun t =>
      Context p (68 :: 20 :: slots) t ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  refine WP.mono (keyBoundSave_store s h count mask) ?_
  rintro t ⟨mem, rest⟩
  let mid := putMem s (s.mem.writeW (off (State.addr s.sp) 20) (BitVec.ofNat 32 p.scalarWidth))
  have midRest : Rest [] s mid := ⟨by intro r _; rfl, rfl, rfl, rfl⟩
  have midCtx := h.store_slot stable 20 (by decide) (by decide) (t := mid) rfl midRest h.ptr
  have midStable : stableSlots (20 :: slots) = true := by
    change (true && stableSlots slots) = true
    rw [Bool.true_and, stable]
  have lastRest : Rest [.r12] mid t := ⟨rest.gpr, rest.rd, rest.wr, rest.sp⟩
  have ctx := midCtx.store_slot midStable 68 (by decide) (by decide) mem lastRest
    ((rest.gpr .r0 (by simp)).trans h.ptr)
  refine ⟨ctx, ?_, rest⟩
  rw [mem]
  exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
    (by simp) _ (Region.contains_self _ _)

end VG.Proof.Ffdh.Arm
