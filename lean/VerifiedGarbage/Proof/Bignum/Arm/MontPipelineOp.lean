module
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipelineOp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineFnBody
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! # Fixed-index Montgomery operations over a proved scanning round -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem montPipelineOp_ok (round : Prog isa) (law : MontPipeline.LoopLaw round) (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (MontPipeline.op round o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [MontPipeline.op, WP.seq_iff]
  refine WP.mono (montOpArgs_ok s ho.1 ha.1 hb.1) ?_
  rintro u ⟨po, pa, pb, memU, restU⟩
  have ready := h.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ptr)
  have body := MontPipeline.fnBody_ok round law u ready.workspace ready.layout ho ha hb ready.ptr po pa pb
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
  have rest : Rest roundClobbers s t := (restU.mono (by decide)).trans
    (restV.trans (restT.mono (by decide)))
  obtain ⟨final, modulus⟩ := h.after_array ho0 keeps frame rest ptr
  exact ⟨final, modulus, bound, value, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
