module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! Operand import from the saved public FFDH pointer and length. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt Keeps)

theorem importArgs_ok (s : State) {p : Inputs} {slots : List Nat} (slot countSlot : Nat)
    (h : Context p slots s) (stable : stableSlots slots = true)
    (hs : slot ∈ slots) (hc : countSlot ∈ slots) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.importArgs slot countSlot)) s fun t =>
      (t.gpr .r4 = p.slotValue slot ∧ t.gpr .r6 = p.slotValue countSlot ∧ t.mem = s.mem) ∧ Rest [.r4, .r6] s t := by
  have bounds (d : Nat) (hd : d ∈ slots) := (stableSlots_at stable hd).1
  have small (d : Nat) (hd : d ∈ slots) : d < 4096 := by have := bounds d hd; omega
  have addr (d : Nat) (hd : d ∈ slots) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := bounds d hd; have := h.locals.space.nowrap; omega)
  have rs := h.locals.read (bounds slot hs)
  have rc := h.locals.read (bounds countSlot hc)
  have vs := h.saved slot hs
  have vc := h.saved countSlot hc
  refine withRest_all [.r4, .r6] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.importArgs
  ffrun [small slot hs, small countSlot hc, addr slot hs, addr countSlot hc, rs, rc, vs, vc, off]

theorem importAt_ok (s : State) {p : Inputs} {slots : List Nat} (a slot countSlot : Nat) {bs : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true) (hs : slot ∈ slots) (hc : countSlot ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s) (ha : a < 8) (na : a ≠ 0)
    (source : Octets p.base (p.slotValue slot) p.len bs s)
    (positive : 0 < bs.length) (fits : bs.length ≤ 8 * p.w)
    (count : p.slotValue countSlot = BitVec.ofNat 32 bs.length) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt a slot countSlot) s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧ numAt t.mem (State.addr p.base) p.w a = Spec.Rsa.os2ip bs ∧
      Keeps (State.addr p.base) p.len p.w a s.mem t.mem ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.importAt, WP.seq_iff]
  refine WP.mono (importArgs_ok s slot countSlot h stable hs hc) ?_
  rintro u ⟨⟨srcU, countU, mem⟩, restU⟩
  have frameU : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem u.mem := by rw [mem]; exact Frame.refl _ _
  have readyU := ready.of_mem mem restU ((restU.gpr .r0 (by simp)).trans ready.ptr)
  have sourceU := source.after_workspace frameU restU
  refine WP.mono (importOperand_ok u readyU ha na positive fits sourceU.fits sourceU.readable
    sourceU.separate srcU (countU.trans count)) ?_
  rintro t ⟨readyT, value, keeps, frameT, restT⟩
  rw [mem, source.bytes] at value
  rw [mem] at keeps frameT
  have rest : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans restT
  exact ⟨h.after_workspace frameT rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1),
    readyT, value, keeps, frameT, rest⟩

end VG.Proof.Ffdh.Arm
