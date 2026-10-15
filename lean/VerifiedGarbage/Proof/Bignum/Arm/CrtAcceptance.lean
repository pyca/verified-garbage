module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtAcceptance
public import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptance
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Copy the validity bit without exposing it in control flow -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

theorem crt_installAcceptance_ok (s : State) {base : BitVec 32} {size : Nat}
    (ws : Workspace s base size) (fit : 216 ≤ size) (ptr : s.gpr .r0 = base)
    (stackFit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4) :
    WP isa (.block installAcceptance) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) 212) (s.mem.readW (off (State.addr s.sp) 48) 32) ∧
      Outside (State.addr base) 212 4 s.mem t.mem ∧ Rest [.r11, .r12] s t := by
  unfold installAcceptance
  refine wp_stackAddr (by decide) fun u h => ?_
  refine wp_ldr (a := off (State.addr s.sp) 48) (by decide)
    (by rw [h.gpr, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [h.rd, h.wr]; exact read) fun v j => ?_
  refine wp_str (a := off (State.addr base) 212) (by decide)
    (by rw [j.other .r0 (by decide), h.other .r0 (by decide), ptr]
        exact addr_add (by have := ws.nowrap; omega))
    (by rw [j.wr, h.wr]; exact ws.write fit) fun t k => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off (State.addr base) 212) (s.mem.readW (off (State.addr s.sp) 48) 32) := by
    rw [k.mem, j.gpr, j.mem, h.mem]
  refine ⟨mem, ?_, (h.rest (by simp)).trans ((j.rest (by simp)).trans ((k.rest []).mono (by simp)))⟩
  rw [mem]
  exact writeW32_outside _ _ _ (by decide)

end VG.Proof.Bignum.Arm
