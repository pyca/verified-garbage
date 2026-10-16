module

public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Advance the exponent byte and decrement its public bit count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str wp_subs op2_reg op2_imm dpVal ofNat_beq_zero)

theorem expDecrement_ok (s : State) {base : BitVec 32} {size c : Nat}
    (ws : Workspace s base size) (fits : 196 ≤ size) (ptr : s.gpr .r0 = base)
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (count : s.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 c) :
    WP isa (.block expDecrement) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) 192) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.r1] s t := by
  have nowrap := ws.nowrap
  have addr : State.addr (s.gpr .r0 + BitVec.ofNat 32 192) = off (State.addr base) 192 := by
    rw [ptr]; exact addr_add (by omega)
  unfold expDecrement
  refine wp_ldr (a := off (State.addr base) 192) (by decide) addr (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  refine wp_str_z (a := off (State.addr base) 192) (by decide)
    (by rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]; exact addr)
    (by rw [u2.wr, u1.wr]; exact ws.write (by omega)) fun t u3 z3 => WP.block_nil ?_
  have value : s2.gpr .r1 = BitVec.ofNat 32 (c - 1) := by
    rw [u2.gpr, u1.gpr, count]
    change BitVec.ofNat 32 c - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
  refine ⟨?_, ?_, (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest _))⟩
  · rw [u3.mem, u2.mem, u1.mem, value]
  · rw [z3, z2, ← u2.gpr, value, ofNat_beq_zero (by omega)]
    simp only [show c - 1 = 0 ↔ c = 1 by omega]


theorem expShift_ok (s : State) {base : BitVec 32} {size V : Nat}
    (ws : Workspace s base size) (fits : 204 ≤ size) (ptr : s.gpr .r0 = base)
    (value : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa (.block expShift) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) 200) (BitVec.ofNat 32 (V + V)) ∧ Rest [.r1] s t := by
  have address : State.addr (s.gpr .r0 + BitVec.ofNat 32 200) = off (State.addr base) 200 := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold expShift
  refine wp_ldr (a := off (State.addr base) 200) (by decide) address (ws.read (by omega)) fun u h => ?_
  refine wp_dp (op2_reg _ _) fun v j => ?_
  refine wp_str (a := off (State.addr base) 200) (by decide)
    (by rw [j.other .r0 (by decide), h.other .r0 (by decide)]; exact address)
    (by rw [j.wr, h.wr]; exact ws.write (by omega)) fun t l => WP.block_nil ?_
  refine ⟨?_, (h.rest (by simp)).trans ((j.rest (by simp)).trans (l.rest _))⟩
  rw [l.mem, j.mem, h.mem, j.gpr, dpVal, h.gpr, value, ← BitVec.ofNat_add]

end VG.Proof.Bignum.Arm
