module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Follow a factor's public parent pointer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem crt_leavePrime_ok (s : State) {base child : BitVec 32} {size : Nat}
    (ws : Workspace s child size) (fit : 220 ≤ size) (ptr : s.gpr .r0 = child)
    (link : s.mem.readW (off (State.addr child) 216) 32 = base) :
    WP isa (.block leavePrime) s fun t => t.gpr .r0 = base ∧ t.mem = s.mem ∧ Rest [.r0] s t := by
  unfold leavePrime
  refine wp_ldr (a := off (State.addr child) 216) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read fit) fun t h =>
    WP.block_nil ⟨h.gpr.trans link, h.mem, h.rest (by simp)⟩

end VG.Proof.Bignum.Arm
