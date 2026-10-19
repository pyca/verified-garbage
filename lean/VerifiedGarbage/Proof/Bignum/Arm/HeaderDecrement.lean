module

public import VerifiedGarbage.Impl.Bignum.Arm.HeaderControl
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Decrement a fixed-offset public loop counter -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str wp_subs op2_reg op2_imm dpVal ofNat_beq_zero)

theorem headerDecrement_ok (s : State) {base : BitVec 32} {size c d : Nat}
    (ws : Workspace s base size) (fits : d + 4 ≤ size) (hd : d < 4096) (ptr : s.gpr .r0 = base)
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (count : s.mem.readW (off (State.addr base) d) 32 = BitVec.ofNat 32 c) :
    WP isa (.block (headerDecrement d)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) d) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.r1] s t := by
  have nowrap := ws.nowrap
  have addr : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by omega)
  unfold headerDecrement
  refine wp_ldr (a := off (State.addr base) d) hd addr (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  refine wp_str_z (a := off (State.addr base) d) hd
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


end VG.Proof.Bignum.Arm
