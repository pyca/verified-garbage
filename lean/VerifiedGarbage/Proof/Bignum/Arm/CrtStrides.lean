module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Impl.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Public arithmetic determines the CRT workspace and product strides -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp op2_reg op2_lsl op2_imm dpVal)

theorem crt_linkStride_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 52 ≤ size) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block linkStride) s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 w ∧ t.gpr .r1 = BitVec.ofNat 32 (stride w) ∧ t.gpr .r2 = base ∧
      t.mem = s.mem ∧ Rest [.r7, .r1, .r2] s t := by
  unfold linkStride
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read fit) fun u a => ?_
  refine wp_mov (op2_lsl (by decide)) fun v b => ?_
  refine wp_dp (op2_imm (by decide)) fun z c => ?_
  refine wp_mov (op2_reg _ _) fun t d => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, d.mem.trans (c.mem.trans (b.mem.trans a.mem)),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans (d.rest (by simp))))⟩
  · rw [d.other .r7 (by decide), c.other .r7 (by decide), b.other .r7 (by decide), a.gpr, count]
  · rw [d.other .r1 (by decide), c.gpr, dpVal, b.gpr, a.gpr, count, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 w * BitVec.ofNat 32 128 + BitVec.ofNat 32 512 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    simp only [stride, workspaceWords]
    omega
  · rw [d.gpr, c.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide), ptr]

theorem crt_productStride_ok (s : State) {w : Nat} (count : s.gpr .r7 = BitVec.ofNat 32 w) :
    WP isa (.block productStride) s fun t =>
      t.gpr .r1 = BitVec.ofNat 32 (productBytes w) ∧ t.mem = s.mem ∧ Rest [.r1] s t := by
  unfold productStride
  refine wp_mov (op2_lsl (by decide)) fun u a => ?_
  refine wp_dp (op2_imm (by decide)) fun t b => WP.block_nil ?_
  refine ⟨?_, b.mem.trans a.mem, (a.rest (by simp)).trans (b.rest (by simp))⟩
  rw [b.gpr, dpVal, a.gpr, count, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 w * BitVec.ofNat 32 16 + BitVec.ofNat 32 8 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  congr 1
  simp only [productBytes, productWords]
  omega

end VG.Proof.Bignum.Arm
