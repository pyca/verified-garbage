module

public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Load the current public exponent byte through its saved pointer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_ldrb)

theorem expByteLoad_ok (s : State) {base ep : BitVec 32} {size : Nat}
    (ws : Workspace s base size) (fits : 132 ≤ size) (ptr : s.gpr .r0 = base)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) 1) :
    WP isa (.block expByteLoad) s fun t => t.gpr .r1 = (s.mem (State.addr ep)).setWidth 32 ∧
      t.mem = s.mem ∧ Rest [.r1, .r2] s t := by
  unfold expByteLoad
  refine wp_ldr (a := off (State.addr base) 128) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read (by omega)) fun u h => ?_
  refine wp_ldrb (a := State.addr ep) (by decide)
    (by rw [h.gpr, pointer, BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact read) fun t j => WP.block_nil ?_
  exact ⟨by rw [j.gpr, h.mem], j.mem.trans h.mem, (h.rest (by simp)).trans (j.rest (by simp))⟩

end VG.Proof.Bignum.Arm
