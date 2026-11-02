module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math

/-! One shared Montgomery product combines a table entry with the public basis. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

theorem product6_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {exponent low : Nat}
    (h : Core p sp s) (power : Power5 p exponent s)
    (selected : numAt s.mem (State.addr p.base) p.w 1 = entryValue p low) :
    WP isa (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 6 1 5) s fun t =>
      Core p sp t ∧ Power5 p exponent t ∧
      numAt t.mem (State.addr p.base) p.w 6 =
        VG.Spec.Rsa.powMod p.G (VG.Spec.Rsa.FixedBaseComb.exponent (bits p) low + exponent) p.P * 2^(64*p.w) % p.P ∧
      Keeps (State.addr p.base) p.len p.w 6 s.mem t.mem ∧
      Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  let K := TwoExp.sharedMontgomery p.base sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have persistent : TwoExp.CallReady p.base sp p.len s := ⟨h.memory.calls.stack,h.memory.fixed⟩
  have operand : Operand 5 := by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
  have positive : 0 < p.P := by have := h.memory.ready.modulus; rw [h.modulus] at this; omega
  have bound : numAt s.mem (State.addr p.base) p.w 5 < numAt s.mem (State.addr p.base) p.w 0 := by
    rw [h.modulus,power]
    exact Nat.mod_lt _ positive
  refine WP.mono (K.op_ok s 6 1 5 h.memory.ready persistent (by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) (by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]) operand (by decide) bound) ?_
  rintro t ⟨ready,_,canonical,value,keeps,_,frame,rest⟩
  have frame' : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem := by
    simpa only [K,h.memory.fixed] using frame
  have memory := h.memory.after_arithmetic ready frame' rest
  have core := h.after_array memory keeps (by decide) (by decide) (by decide)
  rw [h.modulus] at canonical value
  have encoded := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded
    (VG.Proof.Bignum.coprime_pow2 h.odd (64*p.w)) canonical (show numAt s.mem (State.addr p.base) p.w 1 = _ from selected) power value
  have fit := h.memory.ready.width ▸ h.memory.ready.layout.2.2.1
  have powerT : Power5 p exponent t := (keeps_array_num keeps fit operand (by decide)).trans power
  exact ⟨core,powerT,encoded,keeps,frame',rest⟩


theorem product_entry_value (p : Inputs) {j low : Nat} (hj : j < 5) (hlow : low < 2^j) :
    VG.Spec.Rsa.powMod p.G
      (VG.Spec.Rsa.FixedBaseComb.exponent (bits p) low + 2^(j*VG.Spec.Rsa.FixedBaseComb.rows (bits p))) p.P *
      2^(64*p.w) % p.P = entryValue p (2^j+low) := by
  unfold entryValue
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth (bits p) j low hj hlow]

end VG.Proof.Ffdh.Arm.CombBuilder
