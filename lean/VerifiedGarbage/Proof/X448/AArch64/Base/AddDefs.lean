import VerifiedGarbage.Proof.X448.AArch64.Fast.StepOps
import VerifiedGarbage.Proof.X448.BaseAdd
import VerifiedGarbage.Proof.X448.AArch64.Base.Const

/-!
# X448 of the base point on AArch64: what the additions' proofs share

Untrusted: everything here is checked by Lean. The point in three slots, the
temporaries, `Same.mono`, slot 19's zero, the counters' step and
the bound of a constant, apart from the proofs of the
additions with AdvSIMD (`Add.lean`), so that the scalar addition
(`AddGen.lean`) does not import them.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Impl.X448.AArch64.Base (limb)
open VG.Proof.X448.AArch64 (Keeps limbs word)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (Same Bnd)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Spec.Ed448 (Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The point in slots `x`, `y`, `z`. -/
def pt (e : Env) (x y z : Index) : Point := ⟨e x, e y, e z⟩

/-- The temporaries. -/
def temps : List Index := [10, 11, 12, 13, 14, 15, 16, 17, 18]

theorem Same.mono {base : Addr} {l l' : List Index} {m m' : Mem} (h : Same base l m m')
    (hl : ∀ i ∈ l, i ∈ l') : Same base l' m m' := fun i hi j hj => h i (fun e => hi (hl i e)) j hj

theorem zero_env {m : Mem} {base : Addr} (h : ∀ w < 8, limbs m base (slot (19 : Index).val) w = 0) :
    EV m base 19 = 0 ∧ Bnd Mb m base (slot (19 : Index).val) := by
  refine ⟨?_, fun w hw => by rw [h w hw]; decide⟩
  show VG.Proof.X448.AArch64.Weak.F m base (slot (19 : Index).val) = 0
  simp only [VG.Proof.X448.AArch64.Weak.F]
  rw [VG.Proof.X448.Wide.valN_congr h]
  have : VG.Proof.X448.Wide.valN (fun _ => 0) 8 = 0 := by decide
  rw [this]; rfl

theorem next_fact {n j : Nat} (hn : n ≤ 57) (hj : j < n) :
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 n != 0) = decide (j + 1 ≠ n)) := by
  refine ⟨(BitVec.ofNat_add _ _).symm, Bool.eq_iff_iff.mpr ?_⟩
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  bv_omega_using [hn, hj]

theorem next_ok (s : State) {n j : Nat} (hn : n ≤ 57) (hj : j < n) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block ([.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n] : List Instr)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x9 != 0) = decide (j + 1 ≠ n) ∧
      Keeps [.x19, .x9] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (1 : Nat) < 4096 from by decide, show n < 4096 by omega, ite_true,
    RegUpd.gpr_write, BitVec.setWidth_eq, hc, (next_fact hn hj).1, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (next_fact hn hj).2, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- The counter's step, the comb's end at `x30 = n`. -/
theorem nextR_ok (s : State) {n j : Nat} (hn : n ≤ 57) (hj : j < n) (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (h1 : s.gpr .x30 = BitVec.ofNat 64 n) :
    WP isa (.block ([.addImm .x .x19 .x19 1, .sub .x .x9 .x19 .x30] : List Instr)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x9 != 0) = decide (j + 1 ≠ n) ∧
      Keeps [.x19, .x9] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (1 : Nat) < 4096 from by decide, ite_true,
    RegUpd.gpr_write, BitVec.setWidth_eq, hc, (next_fact hn hj).1, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', h1]
  refine ⟨trivial, (next_fact hn hj).2, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bnd_of_words {m : Mem} {base : Addr} {o : Nat} {v : Spec.X448.Fe}
    (h : ∀ w < 8, word m base (o + 8 * w) = limb v w) : Bnd Ib m base o := fun w hw => by
  show (word m base (o + 8 * w)).toNat < _
  rw [h w hw]; exact Nat.lt_of_lt_of_le (limb_lt v w) (by decide)

end VG.Proof.X448.AArch64.Base
