module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Save the parent link and enter a factor workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str wp_mov op2_reg op2_imm)

theorem crt_primeEnter_ok (s : State) {child : BitVec 32} {size : Nat}
    (ws : Workspace s child size) (fit : 220 ≤ size) (ptr : s.gpr .r2 = child) :
    WP isa (.block primeEnter) s fun t =>
      t.gpr .r0 = child ∧ t.gpr .r3 = 0 ∧
      t.mem = s.mem.writeW (off (State.addr child) 216) (s.gpr .r0) ∧ Rest [.r0, .r3] s t := by
  unfold primeEnter
  refine wp_str (a := off (State.addr child) 216) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.write fit) fun u a => ?_
  refine wp_mov (op2_reg _ _) fun v b => ?_
  refine wp_mov (op2_imm (by decide)) fun t c => WP.block_nil ?_
  have restA : Rest [] s u := a.rest []
  exact ⟨(c.other .r0 (by decide)).trans (b.gpr.trans ((restA.gpr .r2 (by simp)).trans ptr)),
    c.gpr, by rw [c.mem, b.mem, a.mem], (restA.mono (by simp)).trans ((b.rest (by simp)).trans (c.rest (by simp)))⟩

end VG.Proof.Bignum.Arm
