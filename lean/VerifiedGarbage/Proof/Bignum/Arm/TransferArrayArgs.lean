module

public import VerifiedGarbage.Impl.Bignum.Arm.TransferArray
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Select public source and destination arrays across workspaces -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_reg op2_imm)

theorem transferArrayArgs_ok (s : State) {base src dst : BitVec 32} {size o a : Nat}
    (ws : Workspace s base size) (fit : 128 ≤ size) (ho : o < 8) (ha : a < 8)
    (ptr : s.gpr .r0 = base) (source : s.gpr .r1 = src)
    (array : s.mem.readW (off (State.addr base) (64 + 8 * o)) 32 = dst) :
    WP isa (.block (transferArrayArgs o a)) s fun t =>
      t.gpr .r0 = src ∧ t.gpr .r4 = dst ∧ t.gpr .r2 = BitVec.ofNat 32 a ∧
      t.mem = s.mem ∧ Rest [.r0, .r2, .r4] s t := by
  have enc : ∀ i : Fin 8, encodable (BitVec.ofNat 32 i.val) = true := by decide
  unfold transferArrayArgs
  refine wp_ldr (a := off (State.addr base) (64 + 8 * o)) (by omega)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read (by omega)) fun u h => ?_
  refine wp_mov (op2_reg _ _) fun v j => ?_
  refine wp_mov (op2_imm (enc ⟨a, ha⟩)) fun t k => WP.block_nil ?_
  exact ⟨(k.other .r0 (by decide)).trans (j.gpr.trans ((h.other .r1 (by decide)).trans source)),
    (k.other .r4 (by decide)).trans ((j.other .r4 (by decide)).trans (h.gpr.trans array)),
    k.gpr, k.mem.trans (j.mem.trans h.mem),
    (h.rest (by simp)).trans ((j.rest (by simp)).trans (k.rest (by simp)))⟩

end VG.Proof.Bignum.Arm
