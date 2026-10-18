module

public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! # Initialize the public R-squared loop count to 65*w -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str op2_lsl dpVal)

theorem r2CountInit_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fits : 212 ≤ size) (ptr : s.gpr .r0 = base)
    (width : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block r2CountInit) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) 208) (BitVec.ofNat 32 (65 * w)) ∧ Rest [.r1] s t := by
  have nowrap := ws.nowrap
  have a48 : State.addr (s.gpr .r0 + BitVec.ofNat 32 48) = off (State.addr base) 48 := by
    rw [ptr]; exact addr_add (by omega)
  have a208 : State.addr (s.gpr .r0 + BitVec.ofNat 32 208) = off (State.addr base) 208 := by
    rw [ptr]; exact addr_add (by omega)
  unfold r2CountInit
  refine wp_ldr (a := off (State.addr base) 48) (by decide) a48 (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_str (a := off (State.addr base) 208) (by decide)
    (by rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]; exact a208)
    (by rw [u2.wr, u1.wr]; exact ws.write (by omega)) fun t u3 => WP.block_nil ?_
  refine ⟨?_, (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest _))⟩
  rw [u3.mem, u2.mem, u1.mem, u2.gpr, dpVal, u1.gpr, width, BitVec.shiftLeft_eq_mul_twoPow]
  change s.mem.writeW _ (BitVec.ofNat 32 w + BitVec.ofNat 32 w * BitVec.ofNat 32 64) = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  congr 2
  omega

end VG.Proof.Bignum.Arm
