import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# The comb from tables in memory on AArch64: the selection's scalar parts

The parts of the selection (`TCombSelectV`) on general registers: the
table's address into `x16`, from the static `tsym`'s plus `j` tables, with
`x7 = 0` and `x5 = 1` (`selSetup_ok`), and `Z = R` unless the magnitude is
zero, by the carry of `subs` (`selZ_carry`) and `csel` (`zWords_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem entryRegs_regs : ∀ n ≤ 9, ∀ r ∈ entryRegs n,
    r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x19] := by decide

/-- The carry after `subs _, x, 1` is set exactly if `x ≠ 0`. -/
theorem carry_sub_one (x : BitVec 64) :
    decide (2 ^ 64 ≤ x.toNat + (~~~(BitVec.ofNat 64 1)).toNat + (true).toNat) = decide (x ≠ 0) := by
  have h1 : (~~~(BitVec.ofNat 64 1)).toNat = 2 ^ 64 - 2 := by decide
  rw [h1]
  have := x.isLt
  by_cases h : x = 0
  · subst h; decide
  · have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [Bool.toNat_true, h, ne_eq, not_false_eq_true, decide_true, decide_eq_true_eq]
    omega

/-- `x16` = table `j`'s address, `x7 = 0`, `x5 = 1` and `x1 = 0`. -/
theorem selSetup_ok (K : TCombCfg) {s : State}
    {j : Nat} {T : Addr} (hx19 : s.gpr .x19 = BitVec.ofNat 64 j) (hT : s.syms K.tsym = T)
    (htb : K.tblBytes < 65536) :
    WP isa (.block K.selSetup) s fun t =>
      t.gpr .x16 = T + BitVec.ofNat 64 (j * K.tblBytes) ∧ t.gpr .x7 = 0 ∧ t.gpr .x5 = 1 ∧
        t.gpr .x1 = 0 ∧ Keeps [.x1, .x5, .x7, .x16, .x17] s t := by
  rw [TCombCfg.selSetup, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono_syms (movz0_ok s .x7) fun s₁ ⟨z₀, k₁⟩ sy₁ => ?_
  have h19 : s₁.gpr .x19 = BitVec.ofNat 64 j := by rw [k₁.gpr _ (by decide), hx19]
  have h7 : s₁.gpr .x7 = 0 := z₀
  have e₁ : s₁.syms K.tsym = T := by rw [sy₁, hT]
  have hrest : WP isa (.block ([.adrSym .x16 K.tsym, .movz .x .x17 (BitVec.ofNat 16 K.tblBytes) 0,
      .mul .x .x17 .x19 .x17, .add .x .x16 .x16 .x17, .movz .x .x5 1 0, .movz .x .x1 0 0] : List Instr))
      s₁ fun t =>
      t.gpr .x16 = T + BitVec.ofNat 64 (j * K.tblBytes) ∧ t.gpr .x7 = 0 ∧ t.gpr .x5 = 1 ∧
        t.gpr .x1 = 0 ∧ Keeps [.x1, .x5, .x16, .x17] s₁ t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      show 16 * 0 < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
      ite_false, reduceCtorEq, h19, h7, e₁, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    · congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
        Nat.shiftLeft_eq, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Size.bits,
        Nat.mod_eq_of_lt (show K.tblBytes < 2 ^ 16 by omega), Nat.mod_mod]
      rw [← Nat.mul_mod]
    all_goals first | rfl | trivial | skip
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  refine WP.mono hrest fun t ⟨e16, e7, e5, e1, kt⟩ => ⟨e16, e7, e5, e1, ?_⟩
  exact (k₁.mono (by sub_regs)).trans (kt.mono (by sub_regs))

/-- The words of `Z`: `R`'s word `i` if the carry is set, else zero. -/
theorem zWords_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hx7 : s.gpr .x7 = 0) (hz : K.E.z + 8 * K.M.n ≤ size) (hz8 : K.E.z % 8 = 0) :
    ∀ k ≤ K.M.n, WP isa (.block ((List.range k).flatMap fun i =>
        const64 .x6 (wordOf K.one i) ++ ([.csel .x .x6 .x6 .x7, st .x6 (K.E.z + 8 * i)] : List Instr))) s fun t =>
      (∀ i < k, word t.mem base (K.E.z + 8 * i) = if s.c then wordOf K.one i else 0) ∧
      t.c = s.c ∧ KeepRegs [.x6] s t ∧ Outside base K.E.z (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (zWords_ok K hs hx7 hz hz8 k (by omega)) fun s₁ ⟨e₁, c₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (const64c_ok s₁ .x6 (wordOf K.one k)) fun s₂ ⟨e₂, k₂, c₂'⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    have h7 : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hx7]
    have c₂ : s₂.c = s.c := by rw [c₂', c₁]
    rw [← List.singleton_append, WP.block_append_iff]
    have hsel : WP isa (.block [.csel .x .x6 .x6 .x7]) s₂ fun t =>
        t.gpr .x6 = (if s.c then wordOf K.one k else 0) ∧ Keeps [.x6] s₂ t ∧ t.c = s.c := by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_csel, State.read, e₂, h7, c₂,
        RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.c_write, Option.some.injEq, exists_eq_left']
      refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr),
        rfl, rfl, rfl, rfl⟩, ?_⟩
      · cases s.c <;> simp
      · first | rfl | trivial
    refine WP.mono hsel fun s₃ ⟨e₃, k₃, c₃⟩ => ?_
    have hs₃ := hs₂.of_keeps k₃ (by decide)
    refine WP.mono (st_ok hs₃ (d := K.E.z + 8 * k) (by omega) (by omega) .x6) fun t et => ?_
    have mt : t.mem = s₃.mem.writeW (off base (K.E.z + 8 * k)) (s₃.gpr .x6) := by rw [et]
    have kt : KeepRegs [] s₃ t := by subst et; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    have ct : t.c = s₃.c := by rw [et]
    have O₂ : Outside base (K.E.z + 8 * k) 8 s₃.mem t.mem := by
      rw [mt]; exact writeW_outside _ _ _ (by omega)
    have hm₃ : s₃.mem = s₁.mem := by rw [k₃.mem, k₂.mem]
    refine ⟨fun i hi => ?_, by rw [ct, c₃], k₁.trans (((Keeps.regs k₂).trans (Keeps.regs k₃)).trans
      (kt.mono fun _ h => absurd h List.not_mem_nil)), ?_⟩
    · rcases Nat.lt_or_ge i k with h | h
      · rw [O₂.word (by omega) (by omega), hm₃, e₁ i h]
      · obtain rfl : i = k := by omega
        rw [mt, word_writeW_self, e₃]

    · refine (O₁.mono (Nat.le_refl _) (by omega)).trans ?_
      rw [← hm₃]
      exact O₂.mono (by omega) (by omega)

/-- The carry after `subs _, x, 1` for `x = a`: set exactly if `1 ≤ a`. -/
theorem selZ_carry (s : State) {a : Nat} (ha : a < 2 ^ 64) (hx2 : s.gpr .x2 = BitVec.ofNat 64 a)
    (hx5 : s.gpr .x5 = 1) :
    WP isa (.block [.subs .x .x4 .x2 .x5]) s fun t => t.c = decide (1 ≤ a) ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.c_addWithCarry,
    hx2, hx5, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, carry_sub_one]
    congr 1
    apply propext
    constructor
    · intro h; by_contra h'; exact h (by rw [show a = 0 by omega]; rfl)
    · intro h e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this
      simp at this; omega
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

/-- Words that no byte of changed. -/
theorem wordsVal_of_bytes {m m' : Mem} {A : Addr} :
    ∀ (k o : Nat), (∀ i < k, ∀ b < 8, m' (A + BitVec.ofNat 64 (o + 8 * i) + BitVec.ofNat 64 b) =
      m (A + BitVec.ofNat 64 (o + 8 * i) + BitVec.ofNat 64 b)) → wordsVal m' A o k = wordsVal m A o k
  | 0, _, _ => rfl
  | k + 1, o, h => by
    have hw : word m' A o = word m A o := Mem.readW_congr fun b hb => by
      have := h 0 (by omega) b (by omega)
      rwa [Nat.mul_zero, Nat.add_zero] at this
    have ih : wordsVal m' A (o + 8) k = wordsVal m A (o + 8) k :=
      wordsVal_of_bytes k (o + 8) fun i hi b hb => by
        have := h (i + 1) (by omega) b hb
        rwa [show o + 8 * (i + 1) = o + 8 + 8 * i by omega] at this
    simp only [wordsVal, hw, ih]

end VG.Proof.Weierstrass.AArch64
