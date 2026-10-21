module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory

/-! Subgroup membership is a native power followed by a fixed-width equality. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem sharedCheckPublicSubgroup_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} (slot : Nat) {bb : List Byte}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (hb : slot ∈ slots) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots) (hasQ : p.hasQ = true)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (baseBytes : Octets p.base (p.slotValue slot) p.len bb s) (baseLength : bb.length = p.k) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) slot) s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧
      t.gpr .r11 = (if Spec.Rsa.powMod (Spec.Rsa.os2ip bb) p.Q p.P = 1 then 1 else 0) ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup, WP.seq_iff]
  refine WP.mono (sharedCheckPublicPublicPower_ok backend s slot 60 32 h calls stable hb h60 h32 h32 ready modulus odd r2 baseBytes baseLength
    (h.qBytes hasQ) (by rw [p.qLength hasQ]; have := p.minLength; omega)
    (by rw [p.qLength hasQ]; have := p.maxLength; omega) (by change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ])
    (by
      change Region.Disjoint ⟨State.addr p.q, _⟩ _
      rw [p.qLength hasQ]
      exact calls.domainSlice h (by have := p.minLength; omega)
        (by rw [p.domainLength, hasQ]; simp only [ite_true]; omega))) ?_
  rintro u ⟨contextU, readyU, power, modU, r2U, _, frameU, restU⟩
  refine WP.mono (isOne_ok u readyU (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 6) (by decide)) ?_
  rintro t ⟨readyT, flag, arraysT, frameT, restT⟩
  rw [power] at flag
  have frame := frameU.trans (frameT.mono (by simp))
  have rest := restU.trans restT
  exact ⟨h.after_arithmetic calls frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1), readyT,
    flag, (arraysT 0 (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans modU,
    (arraysT 4 (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans r2U,
    frame, rest⟩

end VG.Proof.Ffdh.Arm
