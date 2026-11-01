module

import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont

/-! One shared Montgomery square doubles the encoded public exponent. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

theorem square5_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {exponent : Nat}
    (h : Core p sp s) (power : Power5 p exponent s) :
    WP isa (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5) s fun t =>
      Core p sp t ∧ Power5 p (2*exponent) t ∧
      Keeps (State.addr p.base) p.len p.w 5 s.mem t.mem ∧
      Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  let K := TwoExp.sharedMontgomery p.base sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have persistent : TwoExp.CallReady p.base sp p.len s := ⟨h.memory.calls.stack,h.memory.fixed⟩
  have operand : Operand 5 := by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
  have positive : 0 < p.P := by have := h.memory.ready.modulus; rw [h.modulus] at this; omega
  have bound : numAt s.mem (State.addr p.base) p.w 5 < numAt s.mem (State.addr p.base) p.w 0 := by
    rw [h.modulus,power]
    exact Nat.mod_lt _ positive
  refine WP.mono (K.op_ok s 5 5 5 h.memory.ready persistent operand operand operand (by decide) bound) ?_
  rintro t ⟨ready,_,canonical,value,keeps,_,frame,rest⟩
  have frame' : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem := by
    simpa only [K,h.memory.fixed] using frame
  have memory := h.memory.after_arithmetic ready frame' rest
  have core := h.after_array memory keeps (by decide) (by decide) (by decide)
  rw [h.modulus] at canonical value
  have encoded := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded
    (VG.Proof.Bignum.coprime_pow2 h.odd (64*p.w)) canonical power value
  exact ⟨core,encoded,keeps,frame',rest⟩

end VG.Proof.Ffdh.Arm.CombBuilder
