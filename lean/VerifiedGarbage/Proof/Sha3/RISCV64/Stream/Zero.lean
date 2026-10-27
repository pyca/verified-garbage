module

public import VerifiedGarbage.Impl.Sha3.RISCV64.Zero
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-!
# SHA-3 on RISC-V: zeroing a state

`zeroState b` sets the state at `b` to the sponge's initial state
(`zeroState_ok`), writing only its 200 bytes and `t0`.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Spec.Sha3 (stateAt)

/-- After zeroing `k` lanes from `s₁`, whose `t0` is zero. -/
structure ZInv (b : Reg) (s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp
  frame : Frame [⟨s₁.gpr b, 200⟩] s₁.mem s.mem
  zero : ∀ j < k, s.mem.readW (s₁.gpr b + BitVec.ofNat 64 (8 * j)) 64 = 0

theorem stateAt_zero {m : Mem} {p : Addr} (h : ∀ j < 25, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Spec.Sha3.zero, Vector.getElem_replicate]
  exact h i hi

theorem zeroLanes_ok (b : Reg) {s₁ : State} (h0 : s₁.gpr .t0 = 0) (hal : (s₁.gpr b).toNat % 8 = 0)
    (hwr : ∀ k < 25, InRegions s₁.wr (s₁.gpr b + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block ((List.range 25).flatMap fun k => [.store .d .t0 b (8 * k)])) s₁ (ZInv b s₁ 25) := by
  refine wp_range_flatMap (M := isa) (ZInv b s₁) (fun k s hk h => ?_) 25 (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  refine wp_sd (a := s₁.gpr b + BitVec.ofNat 64 (8 * k)) (by omega) (by rw [h.gpr])
    (Spill.al8 hal (by omega)) (by rw [h.wr]; exact hwr k hk) fun t u => WP.block_nil ?_
  refine ⟨by rw [u.gpr, h.gpr], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.sp, h.sp], ?_, fun j hj => ?_⟩
  · rw [u.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [u.mem, h.gpr, h0]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.zero j (by omega)

/-- `zeroState b`: the state at `b` zeroed, nothing else written but `t0`. -/
theorem zeroState_ok {b : Reg} (hb : b ≠ .t0) {s : State} (hal : (s.gpr b).toNat % 8 = 0)
    (hwr : ∀ k < 25, InRegions s.wr (s.gpr b + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (Impl.Sha3.RISCV64.zeroState b)) s fun t =>
      (∀ r, r ≠ .t0 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr b, 200⟩] s.mem t.mem ∧ stateAt t.mem (s.gpr b) = Spec.Sha3.zero := by
  unfold Impl.Sha3.RISCV64.zeroState
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  have e : s₁.gpr b = s.gpr b := u₁.other _ hb
  refine WP.mono (zeroLanes_ok b u₁.gpr (by rw [e]; exact hal) (by rw [u₁.wr, e]; exact hwr)) fun t h => ?_
  refine ⟨fun r hr => by rw [h.gpr, u₁.other _ hr], by rw [h.rd, u₁.rd], by rw [h.wr, u₁.wr],
    by rw [h.sp, u₁.sp], ?_, stateAt_zero fun j hj => ?_⟩
  · rw [← e, ← u₁.mem]; exact h.frame
  · rw [← e]; exact h.zero j hj

end VG.Proof.Sha3.RISCV64.Stream
