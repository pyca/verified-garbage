module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Select the public destination and modulus array for padding -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_imm)

theorem crt_padModulusArgs_ok (s : State) {base dst : BitVec 32} {size : Nat}
    (ws : Workspace s base size) (fit : 244 ≤ size) (ptr : s.gpr .r0 = base)
    (link : s.mem.readW (off (State.addr base) 240) 32 = dst) (operand : Fin 8 := 0) :
    WP isa (.block (padModulusArgs operand)) s fun t => t.gpr .r4 = dst ∧ t.gpr .r2 = BitVec.ofNat 32 operand.val ∧
      t.mem = s.mem ∧ Rest [.r2, .r4] s t := by
  have enc : ∀ i : Fin 8, encodable (BitVec.ofNat 32 i.val) = true := by decide
  unfold padModulusArgs
  refine wp_ldr (a := off (State.addr base) 240) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read fit) fun u h => ?_
  refine wp_mov (op2_imm (enc operand)) fun t j => WP.block_nil ?_
  exact ⟨(j.other .r4 (by decide)).trans (h.gpr.trans link), j.gpr,
    j.mem.trans h.mem, (h.rest (by simp)).trans (j.rest (by simp))⟩

end VG.Proof.Bignum.Arm
