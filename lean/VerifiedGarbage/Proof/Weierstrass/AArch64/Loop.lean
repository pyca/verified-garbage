import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Impl.Weierstrass.AArch64

/-!
# Short Weierstrass curves on AArch64: loops counted down in `x19`

The ladder, the powers and the tables of bits loop with `x19` counting down:
the body starts with `sub x19, x19, #1`, and the loop runs while `x19 ≠ 0`
(`cbnz`). `countLoop_ok` runs such a loop `n ≥ 1` times from an invariant
indexed by `x19`; `decCounter_ok` is the body's first instruction.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- A loop whose body takes the invariant from `j` to `j - 1` and leaves
`x19 = j - 1`, run from `n ≥ 1`. -/
theorem countLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hn64 : n < 2 ^ 64)
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.gpr .x19 = BitVec.ofNat 64 (j - 1))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body (.nonzero .x .x19)) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  have hx : (s'.read .x .x19 != 0) = decide (j - 1 ≠ 0) := by
    rw [read_x, hz]
    by_cases hj : j - 1 = 0
    · rw [hj]; rfl
    · rw [decide_eq_true hj, bne_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact hj this
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show some (s'.read .x .x19 != 0) = some false
    rw [hx, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show some (s'.read .x .x19 != 0) = some true
    rw [hx, decide_eq_true hj]

theorem decCounter_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hb : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [decCounter]) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ Keeps [.x19] s s' := by
  apply WP.of_runBlock
  simp only [decCounter, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left', hb]
  dsimp only [Size.bits]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt (by omega : j - 1 < 2 ^ 64)]
    omega
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `x19 = j`, for `j < 2¹⁶`. -/
theorem setCounter_ok (s : State) {j : Nat} (hj : j < 2 ^ 16) :
    WP isa (.block [.movz .x .x19 (BitVec.ofNat 16 j) 0]) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 j ∧ Keeps [.x19] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_eq, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

end VG.Proof.Weierstrass.AArch64
