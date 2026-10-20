module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallSquareU
import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
import VerifiedGarbage.Proof.Bignum.Arm.SquareUmaalOp
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallArithmetic

/-! Public operand equality selects one verified UMAAL diagonal square. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest wp_cmp op2_reg)

theorem montCallSquareUArithmetic_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : CallBodyReady base len w o a b s)
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    WP isa MontCallSquareU.arithmetic s fun t =>
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [MontCallSquareU.arithmetic, MontCallWith.dispatch, WP.seq_iff]
  refine wp_cmp (op2_reg s .r12) fun u flags eq => WP.block_nil ?_
  have mem := flags.mem
  have rest := flags.rest []
  have ready := h.of_mem mem rest
  refine WP.ite u.z rfl ?_ ?_
  · intro same
    have indices : a = b := by
      have eq' : BitVec.ofNat 32 a = BitVec.ofNat 32 b := by
        rw [← h.input.aIndex, ← h.input.bIndex]
        have hz : s.gpr .r3 - s.gpr .r12 = 0 := by
          simpa only [eq, beq_iff_eq] using same
        calc
          s.gpr .r3 = (s.gpr .r3 - s.gpr .r12) + s.gpr .r12 := (BitVec.sub_add_cancel _ _).symm
          _ = s.gpr .r12 := by rw [hz]; exact BitVec.zero_add _
      have aw : a < 2 ^ 32 := by have := ha.1; omega
      have bw : b < 2 ^ 32 := by have := hb.1; omega
      have natEq := congrArg BitVec.toNat eq'
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt aw, Nat.mod_eq_of_lt bw] using natEq
    subst b
    have body := squareBodyU_ok u ready.input.workspace ready.input.layout ho ha ready.input.ptr
      ready.input.outIndex ready.input.aIndex ready.input.bIndex
      (by rw [ready.input.width]; exact ready.input.inverse)
      (by rw [ready.input.width]; exact ready.input.operand)
      ready.stackRead ready.stackSep ready.saved
    simp only [ready.input.width] at body
    refine WP.mono body ?_
    rintro t ⟨lt, value, keeps, frame, rt⟩
    rw [mem] at lt value keeps frame
    exact ⟨lt, value, keeps, frame, (rest.mono (by simp)).trans rt⟩
  · intro _
    have body := montFnBody_ok u ready.input.workspace ready.input.layout ho ha hb ready.input.ptr
      ready.input.outIndex ready.input.aIndex ready.input.bIndex
      (by rw [ready.input.width]; exact ready.input.inverse)
      (by rw [ready.input.width]; exact ready.input.operand)
    simp only [ready.input.width] at body
    refine WP.mono body ?_
    rintro t ⟨lt, value, keeps, frame, rt⟩
    rw [mem] at lt value keeps frame
    exact ⟨lt, value, keeps, frame, (rest.mono (by simp)).trans rt⟩

end VG.Proof.Bignum.Arm
