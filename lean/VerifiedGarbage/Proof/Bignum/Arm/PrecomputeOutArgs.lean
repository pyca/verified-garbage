module

public import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut
public import Batteries.Logic
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Advance the RSA precomputation output by one array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp op2_reg op2_imm op2_lsl dpVal)

theorem precomputeOutAdvance_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 52 ≤ size) (ptr : s.gpr .r0 = base)
    (width : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block precomputeOutAdvance) s fun t =>
      t.gpr .r4 = s.gpr .r4 + BitVec.ofNat 32 (8 * w) ∧ t.gpr .r2 = 4 ∧
      t.mem = s.mem ∧ Rest [.r1, .r2, .r4] s t := by
  unfold precomputeOutAdvance
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read fit) fun u h => ?_
  refine wp_mov (op2_lsl (by decide)) fun v j => ?_
  refine wp_dp (op2_reg _ _) fun z l => ?_
  refine wp_mov (op2_imm (by decide)) fun t q => WP.block_nil ?_
  refine ⟨?_, q.gpr, q.mem.trans (l.mem.trans (j.mem.trans h.mem)),
    (h.rest (by simp)).trans ((j.rest (by simp)).trans ((l.rest (by simp)).trans (q.rest (by simp))))⟩
  rw [q.other .r4 (by decide), l.gpr, dpVal, j.other .r4 (by decide), h.other .r4 (by decide),
    j.gpr, h.gpr, width, BitVec.shiftLeft_eq_mul_twoPow]
  change s.gpr .r4 + (BitVec.ofNat 32 w * BitVec.ofNat 32 8) = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

end VG.Proof.Bignum.Arm
