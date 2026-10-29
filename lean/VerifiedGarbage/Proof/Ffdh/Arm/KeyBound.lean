module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.Arm.Isa

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeyBoundArgs
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScan
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.StoreSlot
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanBlocks
import VerifiedGarbage.Proof.Ffdh.KeyScalar
/-! Derive the exact native scalar width and mask from the public domain bound. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyBoundSave.lean`, which only this module imported.
section

/-! Store the public significant width and first-byte mask in native local slots. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeySmear.lean`, which only this module imported.
section

/-! Spread the highest public bound bit into the exact first-byte scalar mask. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

def smear32 (b : Byte) : BitVec 32 :=
  let a := b.setWidth 32 ||| b.setWidth 32 >>> 1
  let c := a ||| a >>> 2
  c ||| c >>> 4

theorem smear32_value (b : Byte) : (smear32 b).toNat = VG.Proof.Ffdh.KeyScalar.smearN b.toNat := by
  simp only [smear32, VG.Proof.Ffdh.KeyScalar.smearN, BitVec.toNat_or,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 32 by have := b.isLt; omega)]

theorem smear32_eq (b : Byte) : smear32 b = BitVec.ofNat 32 (VG.Proof.Ffdh.KeyScalar.smearN b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [smear32_value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have bound := VG.Proof.Ffdh.KeyScalar.smearN_lt b.toNat b.isLt
  omega

theorem smear_ok (s : State) {b : Byte} (byte : s.gpr .r3 = b.setWidth 32) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.smear) s fun t =>
      (t.gpr .r3 = smear32 b ∧ t.mem = s.mem) ∧ VG.Proof.X25519.Arm.Rest [.r3, .r12] s t := by
  refine withRest_all [.r3, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.smear
  ffrun [byte, smear32]

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyBound_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound s fun t =>
      (Context p (68 :: 20 :: slots) t ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem) ∧
      Rest [.r3, .r4, .r6, .r11, .r12] s t := by
  refine withRest_all [.r3, .r4, .r6, .r11, .r12] ?_ (by rfl) (by rfl)
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound, WP.seq_iff]
  refine WP.mono (keyBoundArgs_ok s h h24 h28 h32 h60) ?_
  rintro u ⟨⟨ptr, count, memU⟩, restU⟩
  have ctxU := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  rw [WP.seq_iff]
  refine WP.mono (keyScan_ok u ctxU.boundBytes (by rw [p.boundOctetsLength]; have := p.minLength; omega)
    (by rw [p.boundOctetsLength]; have := p.maxLength; omega) ptr (by rw [p.boundOctetsLength]; exact count)) ?_
  rintro v ⟨_, countV, byteV, memV, restV⟩
  have ctxV := ctxU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans ctxU.ptr)
  rw [WP.block_append_iff]
  refine WP.mono (smear_ok v byteV) ?_
  rintro w ⟨⟨mask, memW⟩, restW⟩
  have ctxW := ctxV.of_mem memW restW ((restW.gpr .r0 (by simp)).trans ctxV.ptr)
  have countW : w.gpr .r6 = BitVec.ofNat 32 p.scalarWidth := by
    rw [restW.gpr .r6 (by simp), countV, p.boundOctetsLength]
    rfl
  have maskW : w.gpr .r3 = p.scalarMask := by
    rw [mask, smear32_eq]
    rfl
  refine WP.mono (keyBoundSave_ok w ctxW stable countW maskW) ?_
  rintro t ⟨ctxT, frame, _⟩
  rw [memW, memV, memU, restW.sp, restV.sp, restU.sp] at frame
  exact ⟨ctxT, frame⟩

end VG.Proof.Ffdh.Arm
