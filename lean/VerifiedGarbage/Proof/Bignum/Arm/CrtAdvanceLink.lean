module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Advance and store a public CRT buffer pointer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_dp wp_str op2_reg dpVal)

theorem crt_advanceLink_ok (s : State) {base : BitVec 32} {size d : Nat}
    (ws : Workspace s base size) (fit : d + 4 ≤ size) (hd : d < 4096) (ptr : s.gpr .r0 = base) :
    WP isa (.block (advanceLink d)) s fun t =>
      t.gpr .r2 = s.gpr .r2 + s.gpr .r1 ∧
      t.mem = s.mem.writeW (off (State.addr base) d) (s.gpr .r2 + s.gpr .r1) ∧ Rest [.r2] s t := by
  unfold advanceLink
  refine wp_dp (op2_reg _ _) fun u h => ?_
  refine wp_str (a := off (State.addr base) d) hd
    (by rw [h.other .r0 (by decide), ptr]; exact addr_add (by have := ws.nowrap; omega))
    (by rw [h.wr]; exact ws.write fit) fun t j => WP.block_nil ?_
  have restJ : Rest [] u t := j.rest []
  refine ⟨?_, ?_, (h.rest (by simp)).trans (restJ.mono (by simp))⟩
  · rw [restJ.gpr .r2 (by simp), h.gpr, dpVal]
  · rw [j.mem, h.mem, h.gpr, dpVal]

end VG.Proof.Bignum.Arm
