module

public import VerifiedGarbage.Impl.Bignum.Arm.DoubleLoop
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Public indices and public counter for the modular-doubling loop -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov wp_ldr wp_subs op2_imm ofNat_beq_zero)

theorem doubleIndices_ok (s : State) :
    WP isa (.block doubleIndices) s fun t =>
      t.gpr .r2 = 4 ∧ t.gpr .r3 = 7 ∧ t.gpr .r12 = 4 ∧
      t.mem = s.mem ∧ Rest [.r2, .r3, .r12] s t := by
  unfold doubleIndices
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u3 => WP.block_nil ?_
  refine ⟨?_, ?_, u3.gpr, u3.mem.trans (u2.mem.trans u1.mem), ?_⟩
  · rw [u3.other .r2 (by decide), u2.other .r2 (by decide), u1.gpr]
  · rw [u3.other .r3 (by decide), u2.gpr]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))

theorem doubleCount_ok (s : State) {base : BitVec 32} {size c : Nat}
    (ws : Workspace s base size) (fits : 212 ≤ size) (ptr : s.gpr .r0 = base)
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (count : s.mem.readW (off (State.addr base) 208) 32 = BitVec.ofNat 32 c) :
    WP isa (.block doubleCount) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) 208) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.r1] s t := by
  have nowrap := ws.nowrap
  have addr : State.addr (s.gpr .r0 + BitVec.ofNat 32 208) = off (State.addr base) 208 := by
    rw [ptr]; exact addr_add (by omega)
  unfold doubleCount
  refine wp_ldr (a := off (State.addr base) 208) (by decide) addr (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  refine wp_str_z (a := off (State.addr base) 208) (by decide)
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
