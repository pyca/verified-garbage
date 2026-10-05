import VerifiedGarbage.Impl.Weierstrass.AArch64.Inv
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop

/-!
# Inversion by divsteps on AArch64: the word divstep

One divstep on words (`wstepCode`) leaves in `x1`–`x7` the words of
`Proof/Divstep/Word.lean`'s `wstep` (`wstepCode_ok`), with `x11 = 1` and
`x12 = 0`; `N` of them, counted down in `x13` (`wstepsLoop_ok`), leave its
`N` steps.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Divstep (WSt wstep)

/-- The words of a divstep: `d`, `f`, `g`, `u`, `v`, `q`, `r` in `x1`–`x7`. -/
def regsW (s : State) : WSt :=
  ⟨s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7⟩

theorem one64 : BitVec.ofNat 64 1 = (1 : BitVec 64) := rfl
theorem two64' : BitVec.ofNat 64 2 = (2 : BitVec 64) := rfl

/-- One divstep on words. -/
theorem wstepCode_ok (s : State) (h11 : s.gpr .x11 = 1) (h12 : s.gpr .x12 = 0) :
    WP isa (.block wstepCode) s fun t =>
      regsW t = wstep (regsW s) ∧ Keeps [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10] s t := by
  apply WP.of_runBlock
  simp only [wstepCode, condAdd, swapAdd, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, read_x, RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte,
    show 63 < Size.x.bits from by decide, show 1 < Size.x.bits from by decide,
    show (1 : Nat) < 4096 from by decide, show (2 : Nat) < 4096 from by decide,
    Option.some.injEq, exists_eq_left', h11, h12, one64, two64']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [regsW, wstep, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
    simp only [RegUpd.gpr_write, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ↓reduceIte]

/-- A loop counted down in `r` (as `countLoop_ok` for `x19`). -/
theorem countLoopR_ok (r : Reg) {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hn64 : n < 2 ^ 64)
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.gpr r = BitVec.ofNat 64 (j - 1))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body (.nonzero .x r)) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  have hx : (s'.read .x r != 0) = decide (j - 1 ≠ 0) := by
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
    show some (s'.read .x r != 0) = some false
    rw [hx, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show some (s'.read .x r != 0) = some true
    rw [hx, decide_eq_true hj]

/-- `x13 -= 1`. -/
theorem dec13_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) (hb : s.gpr .x13 = BitVec.ofNat 64 j) :
    WP isa (.block [.subImm .x .x13 .x13 1]) s fun s' =>
      s'.gpr .x13 = BitVec.ofNat 64 (j - 1) ∧ Keeps [.x13] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (1 : Nat) < 4096 by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', hb]
  dsimp only [Size.bits]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt (by omega : j - 1 < 2 ^ 64)]
    omega
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `N ≥ 1` word divsteps, counted down in `x13`. -/
theorem wstepsLoop_ok {N : Nat} (hN : 1 ≤ N) (hN' : N < 2 ^ 16) (s : State) (h11 : s.gpr .x11 = 1)
    (h12 : s.gpr .x12 = 0) :
    WP isa (Impl.Weierstrass.AArch64.wsteps N) s fun t =>
      regsW t = Divstep.wsteps N (regsW s) ∧
        Keeps [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13] s t := by
  rw [Impl.Weierstrass.AArch64.wsteps]
  refine WP.seq ?_
  have h0 : WP isa (.block [.movz .x .x13 (BitVec.ofNat 16 N) 0]) s fun t =>
      t.gpr .x13 = BitVec.ofNat 64 N ∧ Keeps [.x13] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
      ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_eq, BitVec.toNat_setWidth,
        BitVec.toNat_ofNat]
      omega
    · simp only [List.mem_singleton] at hr; exact RegUpd.gpr_write_of_ne _ _ _ hr
  refine WP.mono h0 fun s₁ ⟨c₁, k₁⟩ => ?_
  have e₁ : regsW s₁ = regsW s := by
    simp only [regsW, k₁.gpr .x1 (by decide), k₁.gpr .x2 (by decide), k₁.gpr .x3 (by decide),
      k₁.gpr .x4 (by decide), k₁.gpr .x5 (by decide), k₁.gpr .x6 (by decide), k₁.gpr .x7 (by decide)]
  refine countLoopR_ok .x13 (n := N) (by omega)
    (Inv := fun j t => regsW t = Divstep.wsteps (N - j) (regsW s) ∧ t.gpr .x11 = 1 ∧ t.gpr .x12 = 0 ∧
      t.gpr .x13 = BitVec.ofNat 64 j ∧ Keeps [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13] s t)
    (fun j t hj1 hjN ⟨rt, t11, t12, t13, kt⟩ => ?_) (fun t ⟨rt, _, _, _, kt⟩ => ⟨by simpa using rt, kt⟩) hN
    ⟨by rw [Nat.sub_self, e₁]; rfl, by rw [k₁.gpr _ (by decide), h11], by rw [k₁.gpr _ (by decide), h12], c₁,
      k₁.mono (by sub_regs)⟩
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (dec13_ok t hj1 (by omega) t13) fun u ⟨xu, ku⟩ => ?_
  refine WP.mono (wstepCode_ok u (by rw [ku.gpr _ (by decide), t11]) (by rw [ku.gpr _ (by decide), t12]))
    fun w ⟨rw', kw⟩ => ⟨⟨?_, by rw [kw.gpr _ (by decide), ku.gpr _ (by decide), t11],
      by rw [kw.gpr _ (by decide), ku.gpr _ (by decide), t12], by rw [kw.gpr _ (by decide), xu],
      ?_⟩, by rw [kw.gpr _ (by decide), xu]⟩
  · have eu : regsW u = regsW t := by
      simp only [regsW, ku.gpr .x1 (by decide), ku.gpr .x2 (by decide), ku.gpr .x3 (by decide),
        ku.gpr .x4 (by decide), ku.gpr .x5 (by decide), ku.gpr .x6 (by decide), ku.gpr .x7 (by decide)]
    rw [rw', eu, rt, show N - (j - 1) = (N - j) + 1 by omega, Divstep.wsteps_succ]
  · exact (kt.trans (ku.mono (by sub_regs))).trans (kw.mono (by sub_regs))

end VG.Proof.Weierstrass.AArch64
