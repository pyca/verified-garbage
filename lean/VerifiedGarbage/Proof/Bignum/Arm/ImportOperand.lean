module

public import VerifiedGarbage.Impl.Bignum.Arm.ImportOperand
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFn
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Framework.Block

/-! # Operand import preserves the modulus, inverse, and all other arithmetic arrays -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Keeps)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem importOperand_ok (s : State) {base src : BitVec 32} {len w o k : Nat}
    (h : ArithmeticReady base len w s) (ho : o < 8) (ho0 : o ≠ 0)
    (positive : 0 < k) (fit : k ≤ 8 * w) (sourceFit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (sep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (importOperand o) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w o = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have enc : ∀ i : Fin 8, encodable (BitVec.ofNat 32 i.val) = true := by decide
  rw [importOperand, WP.seq_iff]
  refine wp_mov (op2_imm (enc ⟨o, ho⟩)) fun u a => WP.block_nil ?_
  have restU : Rest [.r2] s u := a.rest (by decide)
  have ready := h.of_mem a.mem restU ((restU.gpr .r0 (by decide)).trans h.ptr)
  refine WP.mono (loadBEFn_ok u ready.workspace ready.layout ready.width ho positive fit sourceFit
    (by rw [a.rd, a.wr]; exact read) sep ready.ptr a.gpr
    ((a.other .r4 (by decide)).trans source) ((a.other .r6 (by decide)).trans count)
    ready.stackRead ready.stackSep ready.saved) ?_
  rintro t ⟨value, outside, frame, restT, ptr⟩
  rw [a.mem] at value outside frame
  have keeps := outside_array_keeps outside (len := len) (by have := h.workspace.nowrap; omega)
  have rest : Rest roundClobbers s t := (restU.mono (by decide)).trans restT
  exact ⟨(h.after_array ho0 keeps frame rest ptr).1, value, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
