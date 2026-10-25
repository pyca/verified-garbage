module

import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals

/-! Ordinary output buffers and the saved exchange validity result. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure OutputBuffer (dst : BitVec 32) (n : Nat) (s : State) : Prop where
  fits : dst.toNat + n ≤ 2 ^ 32
  writable : InRegions s.wr (State.addr dst) n

theorem OutputBuffer.after {dst : BitVec 32} {n : Nat} {s t : State} {rs : List Reg}
    (h : OutputBuffer dst n s) (rest : Rest rs s t) : OutputBuffer dst n t :=
  ⟨h.fits, by rw [rest.wr]; exact h.writable⟩

theorem saveResult_ok (s : State) {base : BitVec 32} {len : Nat} (locals : Locals base len s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult) s fun t =>
      (t.mem = s.mem.writeW (off (State.addr s.sp) 64) (s.gpr .r11) ∧
        t.mem.readW (off (State.addr s.sp) 64) 32 = s.gpr .r11 ∧
        Frame [⟨off (State.addr s.sp) 64, 4⟩] s.mem t.mem) ∧ Rest [.r12] s t := by
  have addr : State.addr (s.sp + BitVec.ofNat 32 64) = off (State.addr s.sp) 64 :=
    VG.Arm.addr_add (by have := locals.space.nowrap; omega)
  have write := locals.space.write (off := 64) (by decide)
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult VG.Impl.Ffdh.Arm.Domain.st
  ffrun [addr, write, off, BitVec.add_zero]
  exact ⟨Mem.readW_writeW_self32 _ _ _, (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)⟩

end VG.Proof.Ffdh.Arm
