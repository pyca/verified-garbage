import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBytes

/-!
# Ed448 verification's equation on AArch64: the sign of `x`

`zeroSign`'s pieces (its proof is `zeroSignF_ok`, `DecodeSteps.lean`): `x`
fully reduced into `X2`; `x20 |= c`, `c = 0` exactly when `x ≠ 0` or the sign
bit (`x17`) is 0. `negSwap`: `x` swapped with `-x` (slot 12)
by the mask of `x`'s low bit (from `X2`) differing from the sign bit.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs workRegs FieldMem)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv cswapE opSwap)
open VG.Proof.Curve448.AArch64 (mask)
open VG.Impl.X448.AArch64 (ld st slot X2)

theorem orStep_ok {s : State} {base : Addr} (hs : Scr s base) {n : Nat} (hn : n < 16) :
    WP isa (.block ([ld .x4 (X2 + 8 * n), .logic .orr .x .x5 .x5 .x4] : List Instr)) s fun t =>
      t.gpr .x5 = s.gpr .x5 ||| word s.mem base (X2 + 8 * n) ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have r1 := hs.read (d := X2 + 8 * n) (n := 8) (by simp only [X2, slot]; omega)
  have e1 : (X2 + 8 * n) % 8 = 0 ∧ X2 + 8 * n < 4096 * 8 := by simp only [X2, slot]; omega
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
    State.load, State.read, e1, and_self, BitVec.setWidth_eq, hs.x3, r1,
    RegUpd.gpr_write, RegUpd.mem_write, Nat.reduceMul,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `x5` = the OR of `X2`'s sixteen words. -/
theorem orWords_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (([.movz .x .x5 0 0] : List Instr) ++
        (List.range 16).flatMap (fun i => [ld .x4 (X2 + 8 * i), .logic .orr .x .x5 .x5 .x4]))) s fun t =>
      (t.gpr .x5 = 0 ↔ ∀ j < 16, word s.mem base (X2 + 8 * j) = 0) ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movz .x .x5 0 0]) s fun t =>
      t.gpr .x5 = 0 ∧ t.mem = s.mem ∧ Keeps [.x5] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]) fun t0 ⟨z0, m0, k0⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x5 = 0 ↔ ∀ j < n, word s.mem base (X2 + 8 * j) = 0) ∧ u.mem = s.mem ∧ Keeps [.x4, .x5] t0 u
  have step : ∀ n u, n < 16 → inv n u →
      WP isa (.block ([ld .x4 (X2 + 8 * n), .logic .orr .x .x5 .x5 .x4] : List Instr)) u (inv (n + 1)) := by
    intro n u hn ⟨uv, um, uk⟩
    have hsu : Scr u base := (hs.of_keeps k0 (by decide)).of_keeps uk (by decide)
    refine WP.mono (orStep_ok hsu hn) fun v ⟨v5, vm, vk⟩ => ⟨?_, vm.trans um, uk.trans vk⟩
    rw [v5, or_eq_zero64, uv, um]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h1 j hj
      · exact h2
    · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) t0
    ⟨⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => z0⟩, m0, VG.Proof.X448.AArch64.Keeps.refl _ _⟩)
    fun u ⟨uv, um, uk⟩ => ⟨uv, um, (k0.mono (by decide)).trans uk⟩

theorem and17_ok (s : State) :
    WP isa (.block [.logic .and .x .x5 .x5 .x17]) s fun t =>
      t.gpr .x5 = s.gpr .x5 &&& s.gpr .x17 ∧ t.mem = s.mem ∧ Keeps [.x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem valN_zero_iff {f : Nat → Nat} : VG.Proof.X448.valN f 16 = 0 ↔ ∀ j < 16, f j = 0 := by
  constructor
  · intro h j hj
    by_contra hne
    have : 0 < VG.Proof.X448.valN f 16 := by
      rw [show (16 : Nat) = (j + 1) + (15 - j) by omega, VG.Proof.X448.valN_split, VG.Proof.X448.valN]
      have : 0 < VG.Proof.X448.radix ^ j * f j :=
        Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pos_of_ne_zero hne)
      omega
    omega
  · intro h
    rw [VG.Proof.X448.valN_congr (g := fun _ => 0) h]
    clear h
    generalize 16 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [VG.Proof.X448.valN, ih]; rfl

theorem zeroSign_val (z : Bool) {sb : Nat} (hsb : sb < 2) :
    ((if z then (1 : BitVec 64) else 0) &&& BitVec.ofNat 64 sb = 0) ↔ ¬ (z = true ∧ sb = 1) := by
  rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;> cases z <;> decide

/-! ## `-x` swapped in -/

theorem negMask_val (w : BitVec 64) {sb : Nat} (hsb : sb < 2) :
    (0 : BitVec 64) - ((w &&& 1) ^^^ BitVec.ofNat 64 sb) = mask (decide (w.toNat % 2 ^^^ sb = 1)) := by
  have hw : w &&& 1 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hw]
  have h2 : w.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize w.toNat % 2 = a at h2 ⊢
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;> decide

theorem negMask_ok {s : State} {base : Addr} (hs : Scr s base) {sb : Nat} (hsb : sb < 2)
    (h17 : s.gpr .x17 = BitVec.ofNat 64 sb) :
    WP isa (.block negMask) s fun t =>
      t.gpr .x17 = mask (decide (VG.Proof.X448.AArch64.limbs s.mem base X2 0 % 2 ^^^ sb = 1)) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x6, .x17] s t := by
  have r1 := hs.read (d := X2) (n := 8) (by decide)
  have e1 : X2 % 8 = 0 ∧ X2 < 4096 * 8 := by decide
  have e0 : BitVec.setWidth 64 (0 : BitVec 16) = 0 := rfl
  have e1' : BitVec.setWidth 64 (1 : BitVec 16) = 1 := rfl
  apply WP.of_runBlock
  simp only [negMask, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
    State.load, State.read, e1, and_self, BitVec.setWidth_eq, hs.x3, r1, Nat.reduceLT,
    RegUpd.gpr_write, RegUpd.mem_write, Nat.reduceMul, BitVec.shiftLeft_zero,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, e0, e1', h17,
    VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨negMask_val _ hsb, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem mov6_ok (s : State) :
    WP isa (.block [.addImm .x .x6 .x17 0]) s fun t => t.gpr .x6 = s.gpr .x17 ∧ t.mem = s.mem ∧ Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.Ed448.AArch64
