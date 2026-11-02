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
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared

/-! A power from saved FFDH base and exponent buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem sharedCheckPublicPower_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} (bs es ec : Nat)
    {bb eb : List Byte} {M : Nat} (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M)
    (baseBytes : Octets p.base (p.slotValue bs) p.len bb s) (baseLength : bb.length = p.k)
    (exponentBytes : Octets p.base (p.slotValue es) p.len eb s) (exponentPositive : 0 < eb.length)
    (exponentFits : eb.length < 2 ^ 32) (exponentLength : p.slotValue ec = BitVec.ofNat 32 eb.length)
    (exponentBelow : Region.Disjoint ⟨State.addr (p.slotValue es), eb.length⟩ (FrameStack.belowA s.sp 48)) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) bs es ec) s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6 = Spec.Rsa.powMod (Spec.Rsa.os2ip bb) (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr p.base) p.w 0 = M ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M ∧
      numAt t.mem (State.addr p.base) p.w 7 = 1 ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt, WP.seq_iff]
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
  rw [WP.seq_iff]
  refine WP.mono (powerImport_ok u input) ?_
  rintro v ⟨phaseInput, frameV, restV⟩
  let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb z hi => backend.correct z hi ho ha hb) backend.stackOk
  have spV : v.sp = s.sp := restV.sp.trans restU.sp
  have separate : ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48],
      Region.Disjoint ⟨State.addr (p.slotValue es), eb.length⟩ r := by
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r; exact exponentBytes.separate
    · have eq := List.mem_singleton.mp hr; subst r; exact exponentBelow
  refine WP.mono (sharedWindowExpPhase_ok K v phaseInput
    ⟨((calls.after restU).after restV).stack, spV⟩ p.width.2.2.1 separate) ?_
  rintro t ⟨readyT, value, modT, r2T, oneT, _, frameT, restT⟩
  have initial : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48] s.mem v.mem :=
    (frameU.trans frameV).mono (by simp)
  have frame := initial.trans frameT
  have rest : Rest roundClobbers s t :=
    ((restU.mono (by simp [roundClobbers])).trans restV).trans restT
  exact ⟨h.after_arithmetic calls frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1),
    readyT, value, modT, r2T, oneT, frame, rest⟩

end VG.Proof.Ffdh.Arm
