module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Two native words represent each shared 64-bit RSA limb -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str op2_reg dpVal)

theorem crt_productCount_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 148 ≤ size) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block productCount) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 140) (BitVec.ofNat 32 (2 * w))).writeW
        (off (State.addr base) 144) (BitVec.ofNat 32 (2 * w)) ∧ Rest [.r1] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ size) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold productCount
  refine wp_ldr (a := off (State.addr base) 48) (by decide) (addr 48 (by omega)) (ws.read (by omega)) fun u a => ?_
  refine wp_dp (op2_reg _ _) fun v b => ?_
  have doubled : v.gpr .r1 = BitVec.ofNat 32 (2 * w) := by
    rw [b.gpr, dpVal, a.gpr, count, ← BitVec.ofNat_add, show w + w = 2 * w by omega]
  refine wp_str (a := off (State.addr base) 140) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 140 (by omega))
    (by rw [b.wr, a.wr]; exact ws.write (by omega)) fun z c => ?_
  have restC : Rest [] v z := c.rest []
  refine wp_str (a := off (State.addr base) 144) (by decide)
    (by rw [restC.gpr .r0 (by simp), b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 144 (by omega))
    (by rw [restC.wr, b.wr, a.wr]; exact ws.write (by omega)) fun t d => WP.block_nil ?_
  refine ⟨?_, (a.rest (by simp)).trans ((b.rest (by simp)).trans ((restC.mono (by simp)).trans (d.rest _)))⟩
  rw [d.mem, restC.gpr .r1 (by simp), c.mem, doubled, b.mem, a.mem]

end VG.Proof.Bignum.Arm
