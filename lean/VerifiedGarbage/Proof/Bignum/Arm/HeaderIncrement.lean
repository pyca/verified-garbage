module

public import VerifiedGarbage.Impl.Bignum.Arm.HeaderControl
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Increment a fixed-offset workspace pointer or counter -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str op2_imm dpVal)

theorem headerIncrement_ok (s : State) {base : BitVec 32} {size d k : Nat} {value : BitVec 32}
    (ws : Workspace s base size) (fits : d + 4 ≤ size) (hd : d < 4096) (hk : encodable k = true)
    (ptr : s.gpr .r0 = base) (word : s.mem.readW (off (State.addr base) d) 32 = value) :
    WP isa (.block (headerIncrement d k)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) d) (value + BitVec.ofNat 32 k) ∧ Rest [.r1] s t := by
  have address : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold headerIncrement
  refine wp_ldr (a := off (State.addr base) d) hd address (ws.read fits) fun u h => ?_
  refine wp_dp (op2_imm hk) fun v j => ?_
  refine wp_str (a := off (State.addr base) d) hd
    (by rw [j.other .r0 (by decide), h.other .r0 (by decide)]; exact address)
    (by rw [j.wr, h.wr]; exact ws.write fits) fun t l => WP.block_nil ?_
  refine ⟨?_, (h.rest (by simp)).trans ((j.rest (by simp)).trans (l.rest _))⟩
  rw [l.mem, j.mem, h.mem, j.gpr, dpVal, h.gpr, word, BitVec.natCast_eq_ofNat]

end VG.Proof.Bignum.Arm
