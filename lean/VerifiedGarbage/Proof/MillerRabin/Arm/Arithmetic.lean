module
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRounds
public import VerifiedGarbage.Impl.MillerRabin.Arm.Arithmetic
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineFnBody
import VerifiedGarbage.Proof.Bignum.Arm.FiosFastRound
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block

/-! The fused primality-testing kernel preserves the existing fixed-index operation contracts. -/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm.Arithmetic
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Impl.MillerRabin.Arm.Arithmetic
open VG.Proof.Rsa.Mont (Operand numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

private theorem product_fios_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (product true o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Proof.Rsa.Mont.Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  simp only [product, ↓reduceIte]
  rw [WP.seq_iff]
  refine WP.mono (montOpArgs_ok s ho.1 ha.1 hb.1) ?_
  rintro u ⟨po, pa, pb, memU, restU⟩
  have ready := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  have body := MontPipeline.fnBody_ok FiosFast.round (MontPipeline.RoundLaw.loop FiosFast.round_law) u ready.workspace ready.layout ho ha hb ready.ptr po pa pb
    (by rw [ready.width]; exact ready.inverse) (by rw [ready.width, memU]; exact operand)
  simp only [ready.width] at body
  rw [WP.seq_iff]
  refine WP.mono body ?_
  rintro v ⟨bound, value, keeps, frame, restV⟩
  have savedV := saved_base_kept frame ready.stackSep ready.saved restV.sp
  refine WP.mono (restoreBase_ok v (by rw [restV.rd, restV.wr, restV.sp]; exact ready.stackRead) savedV) ?_
  rintro t ⟨ptr, memT, restT⟩
  rw [memU] at bound value keeps frame
  rw [← memT] at bound value keeps frame
  have rest : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans
    (restV.trans (restT.mono (by simp [roundClobbers])))
  obtain ⟨final, modulus⟩ := h.after_array ho0 keeps frame rest ptr
  exact ⟨final, modulus, bound, value, keeps, frame, rest⟩

theorem product_ok (fios : Bool) (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (product fios o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Proof.Rsa.Mont.Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  cases fios with
  | false => exact montOp_ok s h ho ha hb ho0 operand
  | true => exact product_fios_ok s h ho ha hb ho0 operand

theorem square_ok (fios : Bool) (s : State) {base : BitVec 32} {len w o a : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) :
    WP isa (square fios o a) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w a % numAt s.mem (State.addr base) w 0 ∧
      Proof.Rsa.Mont.Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  cases fios with
  | false => exact squareOp_ok s h ho ha ho0 operand
  | true => exact product_fios_ok s h ho ha ha ho0 operand

end VG.Proof.MillerRabin.Arm.Arithmetic
