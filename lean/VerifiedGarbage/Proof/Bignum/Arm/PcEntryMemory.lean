module

public import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
public import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The entry point changes only its two dedicated stack slots -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem pcEntry_memory {s t : State} {base : BitVec 32}
    (mem : t.mem = (s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0)).writeW (State.addr s.sp) base) :
    t.mem.readW (State.addr s.sp) 32 = base ∧
      t.mem.readW (off (State.addr s.sp) 4) 32 = s.gpr .r0 ∧
      Outside (State.addr s.sp) 0 8 s.mem t.mem ∧ Frame [⟨State.addr s.sp, 8⟩] s.mem t.mem := by
  have first := writeW32_outside s.mem (State.addr s.sp) (d := 4) (s.gpr .r0) (by decide)
  have last := writeW32_outside (s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0))
    (State.addr s.sp) (d := 0) base (by decide)
  have outside : Outside (State.addr s.sp) 0 8 s.mem t.mem := by
    rw [mem]
    simpa only [off, BitVec.add_zero] using (first.mono (by decide) (by decide)).trans (last.mono (by decide) (by decide))
  refine ⟨?_, ?_, outside, ?_⟩
  · rw [mem, Mem.readW_writeW_self32]
  · rw [mem]
    have keep := outside_read32 last (d := 4) (by decide) (by decide)
    simp only [off, BitVec.add_zero] at keep
    rw [keep, Mem.readW_writeW_self32]
  · intro a ha
    apply outside a
    have h := ha ⟨State.addr s.sp, 8⟩ (by simp)
    change ¬ ((a - State.addr s.sp).toNat + 1 ≤ 8) at h
    right
    change 8 ≤ (a - State.addr s.sp).toNat
    omega

theorem pcEntry_callee_saved {s t : State} {base : BitVec 32} {g : Reg → BitVec 32}
    (saved : Spill.Saved s.mem (State.addr s.sp) g pcCalleeSaved)
    (mem : t.mem = (s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0)).writeW (State.addr s.sp) base) :
    Spill.Saved t.mem (State.addr s.sp) g pcCalleeSaved := by
  have frame := (pcEntry_memory mem).2.2.2
  apply saved.frame (lo := 16) (hi := 56) (by decide) frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact Offset.disjoint_base _ (by decide) (by decide)

end VG.Proof.Bignum.Arm
