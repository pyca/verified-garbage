module

public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! # Prepare the quotient shift after a Montgomery cancellation row -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp op2_imm dpVal)

theorem shiftArgs_ok (s : State) {base : BitVec 32} {size top acc n : Nat}
    (ws : Workspace s base size) (ht : top + 48 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 top)
    (mn : s.mem.readW (off (State.addr base) (top + 16)) 32 = BitVec.ofNat 32 n)
    (ma : s.mem.readW (off (State.addr base) (top + 44)) 32 = base + BitVec.ofNat 32 acc) :
    WP isa (.block shiftArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 acc ∧ t.gpr .lr = BitVec.ofNat 32 (n + 1) ∧
      t.mem = s.mem ∧ Rest [.r0, .lr] s t := by
  unfold shiftArgs
  refine wp_ldr (by decide) (ws.ea ptr (by omega)) (ws.read (by omega)) fun u hu => ?_
  refine wp_dp (op2_imm (by decide)) fun v hv => ?_
  have wv := (ws.congr hu.wr).congr hv.wr
  have pv := (hv.other .r0 (by decide)).trans ((hu.other .r0 (by decide)).trans ptr)
  refine wp_ldr (by decide) (wv.ea pv (by omega)) (wv.read (by omega)) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, hv.mem, hu.mem, ma]
  · rw [ht.other .lr (by decide), hv.gpr, dpVal, hu.gpr, mn]
    change BitVec.ofNat 32 n + BitVec.ofNat 32 1 = _
    rw [← BitVec.ofNat_add]
  · rw [ht.mem, hv.mem, hu.mem]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest (by simp)))

end VG.Proof.Bignum.Arm
