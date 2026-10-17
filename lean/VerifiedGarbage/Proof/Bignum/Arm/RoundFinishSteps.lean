module

public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Clear the high word and advance the Montgomery round's temporary state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_mov wp_dp wp_subs op2_imm dpVal)

theorem clearTop_ok (s : State) {base : BitVec 32} {size top : Nat}
    (ws : Workspace s base size) (fit : top + 4 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 top) :
    WP isa (.block clearTop) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) top) (0 : BitVec 32) ∧
      t.gpr .r0 = base + BitVec.ofNat 32 (top + 12) ∧ Rest [.r0, .r3] s t := by
  unfold clearTop
  refine wp_mov (op2_imm (by decide)) fun u hu => ?_
  have wu := ws.congr hu.wr
  have pu := (hu.other .r0 (by decide)).trans ptr
  refine wp_str (a := off (State.addr base) top) (by decide) (wu.ea pu (by omega))
    (wu.write fit) fun v hv => ?_
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hu.gpr]
  · rw [ht.gpr, dpVal, hv.gpr, pu]
    change base + BitVec.ofNat 32 top + BitVec.ofNat 32 12 = _
    rw [Offset.add_add]
  · exact (hu.rest (by simp)).trans ((hv.rest _).trans (ht.rest (by simp)))

theorem advanceOperand_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 20 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block advanceOperand) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (tmp + 16))
        (s.mem.readW (off (State.addr base) (tmp + 16)) 32 + 4) ∧ Rest [.r4] s t := by
  unfold advanceOperand
  refine wp_ldr (by decide) (ws.ea ptr (by omega)) (ws.read fit) fun u hu => ?_
  refine wp_dp (op2_imm (by decide)) fun v hv => ?_
  have wv := (ws.congr hu.wr).congr hv.wr
  have pv := (hv.other .r0 (by decide)).trans ((hu.other .r0 (by decide)).trans ptr)
  refine wp_str (by decide) (wv.ea pv (by omega)) (wv.write fit) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hv.gpr, dpVal, hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest _))

theorem decrementRounds_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 24 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block decrementRounds) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (tmp + 20))
        (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 1) ∧
      t.z = (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 1 == 0) ∧ Rest [.lr] s t := by
  unfold decrementRounds
  refine wp_ldr (by decide) (ws.ea ptr (by omega)) (ws.read fit) fun u hu => ?_
  refine wp_subs (op2_imm (by decide)) fun v hv hz => ?_
  have wv := (ws.congr hu.wr).congr hv.wr
  have pv := (hv.other .r0 (by decide)).trans ((hu.other .r0 (by decide)).trans ptr)
  refine wp_str_z (by decide) (wv.ea pv (by omega)) (wv.write fit) fun t ht htz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hv.gpr, hu.gpr]
  · rw [htz, hz, hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest _))

end VG.Proof.Bignum.Arm
