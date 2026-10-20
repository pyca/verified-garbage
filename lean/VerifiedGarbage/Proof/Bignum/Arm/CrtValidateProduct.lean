module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProductState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState
import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProduct
import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProduct
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductValidationState
import VerifiedGarbage.Proof.Framework.Block

/-! # Exact full product validation against the original RSA modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtValidateInput (base : BitVec 32) (size len product cmp pad a b cp cq w : Nat) (s : State) : Prop where
  multiplication : CrtProductInput base size product a b cp cq w s
  comparison : CrtCheckProductInput base size len cmp product pad w s
  separate : 8 * len ≤ product

theorem crt_validationProduct_ready (s : State) {base : BitVec 32} {size len product cmp pad a b cp cq w : Nat}
    (h : CrtValidateInput base size len product cmp pad a b cp cq w s) :
    WP isa factorProduct s fun t => CrtCheckProductInput base size len cmp product pad w t ∧
      val32 t.mem (State.addr base) product (4 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) ∧
      Spec.Rsa.Mont.numAt t.mem (State.addr base) w 0 = Spec.Rsa.Mont.numAt s.mem (State.addr base) w 0 ∧
      Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (crt_factorProduct_ok s h.multiplication) ?_
  rintro t ⟨value, outside, ptr, frame, rest⟩
  rw [show 2 * w + 2 * w + 2 = 4 * w + 2 by omega] at value outside
  obtain ⟨ready, modulus⟩ := h.comparison.after_product h.separate outside frame ptr rest
  exact ⟨ready, value, modulus, outside, frame, rest⟩

theorem crt_validateProduct_ok (s : State) {base : BitVec 32} {size len product cmp pad a b cp cq w : Nat}
    (h : CrtValidateInput base size len product cmp pad a b cp cq w s) :
    WP isa validateProduct s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) =
        Spec.Rsa.Mont.numAt s.mem (State.addr base) w 0 then 1 else 0) ∧
      Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2)),
        (pad, 4 * (4 * w + 2)), (cmp, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [validateProduct, WP.seq_iff]
  refine WP.mono (crt_validationProduct_ready s h) ?_
  rintro u ⟨ready, productU, modulusU, outsideU, frameU, restU⟩
  refine WP.mono (crt_checkProduct_ok u ready) ?_
  rintro t ⟨value, outsideT, frameT, ptrT, restT⟩
  rw [productU, modulusU] at value
  refine ⟨value, ?_, frameU.trans frameT, ptrT, restU.trans restT⟩
  exact (outsideU.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp)).trans (outsideT.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp))

end VG.Proof.Bignum.Arm
