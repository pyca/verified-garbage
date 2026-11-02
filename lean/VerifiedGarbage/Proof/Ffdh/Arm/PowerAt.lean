module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.PowerArgs
import VerifiedGarbage.Proof.Ffdh.Arm.Power
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! A power from saved FFDH base and exponent buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem powerAt_ok (s : State) {p : Inputs} {slots : List Nat} (bs es ec : Nat)
    {bb eb : List Byte} {M : Nat} (h : Context p slots s) (stable : stableSlots slots = true)
    (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M)
    (baseBytes : Octets p.base (p.slotValue bs) p.len bb s) (baseLength : bb.length = p.k)
    (exponentBytes : Octets p.base (p.slotValue es) p.len eb s) (exponentPositive : 0 < eb.length)
    (exponentFits : eb.length < 2 ^ 32) (exponentLength : p.slotValue ec = BitVec.ofNat 32 eb.length) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.powerAt bs es ec) s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6 = Spec.Rsa.powMod (Spec.Rsa.os2ip bb) (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr p.base) p.w 0 = M ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M ∧
      numAt t.mem (State.addr p.base) p.w 7 = 1 ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.powerAt, WP.seq_iff]
  refine WP.mono (powerArgs_ok s bs es ec h stable hb he hc hk) ?_
  rintro u ⟨⟨source, count, exponent, exponentCount, mem⟩, restU⟩
  have frameU : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem u.mem := by rw [mem]; exact Frame.refl _ _
  have readyU := ready.of_mem mem restU ((restU.gpr .r0 (by simp)).trans ready.ptr)
  have baseU := baseBytes.after_workspace frameU restU
  have exponentU := exponentBytes.after_workspace frameU restU
  have input : PowerInput p.base (p.slotValue bs) (p.slotValue es) p.len p.w M bb eb u :=
    ⟨readyU, by rw [mem]; exact modulus, odd, by rw [mem]; exact r2,
      baseU, exponentU, by rw [baseLength]; have := p.minLength; omega,
      by rw [baseLength]; exact p.width.2.2.2.1, exponentPositive, exponentFits,
      source, by rw [baseLength]; exact count, exponent, exponentCount.trans exponentLength⟩
  refine WP.mono (power_ok u input p.width.2.2.1) ?_
  rintro t ⟨readyT, value, modT, r2T, oneT, frameT, restT⟩
  have frame := frameU.trans frameT
  have rest : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans restT
  exact ⟨h.after_workspace frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1),
    readyT, value, modT, r2T, oneT, frame, rest⟩

end VG.Proof.Ffdh.Arm
