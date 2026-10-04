import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Sha3.Arith

/-!
# The scalar resident absorber: advancing to the next block
-/

namespace VG.Proof.Sha3.AArch64.Scalar.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Resident

/-- What advancing changes: `x26`–`x28`, and the data pointer and the length
left in v19 and v20. -/
structure AdvanceKeep (s s' : State) : Prop where
  gpr : ∀ q, q ≠ .x26 → q ≠ .x27 → q ≠ .x28 → s'.gpr q = s.gpr q
  v : ∀ q, q ≠ .v19 → q ≠ .v20 → s'.v q = s.v q
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem advance_ok (s : State) (p : Addr) (n r : Nat) (hr : r ≤ n)
    (hrb : r ≤ 168) (hu : n < 2^63 + r)
    (h19 : vdword (s.v .v19) 0 = p) (h20 : vdword (s.v .v20) 0 = BitVec.ofNat 64 n)
    (h21 : vdword (s.v .v21) 0 = BitVec.ofNat 64 r) :
    WP isa (.block advance) s fun s' => AdvanceKeep s s' ∧
      vdword (s'.v .v19) 0 = p + BitVec.ofNat 64 r ∧
      vdword (s'.v .v20) 0 = BitVec.ofNat 64 (n - r) ∧
      isa.eval (.zero .x .x26) s' = some (decide (r ≤ n - r)) := by
  unfold advance
  refine WP.cons (Sha3.Vector.exec_umov_low s .x26 .v19) (WP.cons (Sha3.Vector.exec_umov_low _ .x27 .v20)
    (WP.cons (Sha3.Vector.exec_umov_low _ .x28 .v21) (WP.cons rfl (WP.cons rfl (WP.cons rfl
      (WP.cons rfl (WP.cons rfl (WP.cons (exec_lsr_x (by decide)) (wp_nil ?_)))))))))
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 r = BitVec.ofNat 64 (n - r) :=
    VG.Proof.Sha3.sub_ofNat hr
  refine ⟨⟨fun q h26 h27 h28 => ?_, fun q h19 h20 => ?_, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write, RegUpd.gpr_setV, h26, h27, h28, ite_false]
  · simp only [RegUpd.v_write, RegUpd.v_setV, h19, h20, ite_false]
  · simp only [RegUpd.v_write, RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, vdword_ofVDwords_0,
      RegUpd.gpr_write, RegUpd.gpr_setV, State.read, Size.bits, BitVec.setWidth_eq, h19, h21]
  · simp only [RegUpd.v_write, RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, vdword_ofVDwords_0,
      RegUpd.gpr_write, RegUpd.gpr_setV, State.read, Size.bits, BitVec.setWidth_eq, h20, h21, hsub]
  · simp only [eval_zero, RegUpd.gpr_write_self, RegUpd.gpr_write, RegUpd.gpr_setV, RegUpd.v_write,
      reduceCtorEq, ite_false, State.read, Size.bits, BitVec.setWidth_eq,
      h20, h21, hsub]
    congr 1
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, Sha3.Vector.enough_iff (n - r) r (by omega) hrb]
    exact and_iff_left (by omega)

end VG.Proof.Sha3.AArch64.Scalar.Resident
