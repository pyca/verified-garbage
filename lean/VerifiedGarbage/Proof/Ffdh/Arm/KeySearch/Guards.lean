module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Framework.Offset

/-! Exact public budget, entropy-room, and continuation guards for key search. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem budgetGuard_ok (s : State) {base : BitVec 32} {j n : Nat}
    (h : Controller base s) (slot : j < 16) (fits : n < 2 ^ 32)
    (value : lowWord s.mem base j = BitVec.ofNat 32 n) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 j, .cmp .r9 (.imm 0)]) s fun t =>
      (t.z = decide (n = 0) ∧ t.mem = s.mem) ∧ Rest [.r9] s t := by
  refine withRest [.r9] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 j, .cmp .r9 (.imm 0)] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord at *
  ffrun [(by omega : 8 * j < 4096), h.addr slot, h.read slot, value]
  change (BitVec.ofNat 32 n - 0#32 == 0#32) = decide (n = 0)
  rw [BitVec.sub_zero]
  exact ofNat_beq_zero fits

theorem roomGuard_ok (s : State) {base : BitVec 32} {remaining width : Nat}
    (h : Controller base s) (remainingFit : remaining < 2 ^ 32) (widthFit : width < 2 ^ 32)
    (length : lowWord s.mem base 10 = BitVec.ofNat 32 remaining)
    (count : lowWord s.mem base 2 = BitVec.ofNat 32 width) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.room) s fun t =>
      (t.z = decide (remaining < width) ∧ t.mem = s.mem) ∧ Rest [.r9, .r10, .r11] s t := by
  refine withRest [.r9, .r10, .r11] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.KeySearch.room : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.room VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord at *
  ffrun [h.addr (by decide : 10 < 16), h.addr (by decide : 2 < 16),
    h.read (by decide : 10 < 16), h.read (by decide : 2 < 16), length, count,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt remainingFit, Nat.mod_eq_of_lt widthFit]
  by_cases room : width ≤ remaining
  · simp only [room, decide_true, ite_true, show ¬remaining < width by omega, decide_false]
    rfl
  · simp only [room, decide_false, show remaining < width by omega, decide_true]
    rfl

theorem statusGuard_ok (s : State) {base : BitVec 32} {status : Nat}
    (h : Controller base s) (small : status < 5)
    (value : lowWord s.mem base 14 = BitVec.ofNat 32 status) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 14, .cmp .r9 (.imm 4)]) s fun t =>
      (t.z = decide (status = 4) ∧ t.mem = s.mem) ∧ Rest [.r9] s t := by
  refine withRest [.r9] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 14, .cmp .r9 (.imm 4)] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord at *
  ffrun [h.addr (by decide : 14 < 16), h.read (by decide : 14 < 16), value]
  have casesStatus : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3 ∨ status = 4 := by omega
  rcases casesStatus with rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Ffdh.Arm.KeySearch
