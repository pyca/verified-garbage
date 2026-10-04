import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# The comb from tables in memory on AArch64: the selection

The entry of the magnitude `a` of table `j`, selected in constant time
(`select_ok`): the table's address into `x16` (from the static `tsym`'s, plus
`j` tables), the registers `entryRegs n` set to `(0, R)`, then for every
entry `m = 1 … H`, `x1 = m`, the carry clear exactly when `a = m`
(`selEntry_ok`), and each of its words loaded and kept by `csel` on the
carry (`cselWords_ok`): after them the registers hold entry `a`'s words if
`1 ≤ a ≤ H`, else `(0, R)` (`entries_ok`). They go to `E`, and `Z` is `R`
unless `a = 0`.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- Register `i` of the entry. -/
def er (n i : Nat) : Reg := (entryRegs n).getD i .x8

theorem er_ne : ∀ n ≤ 4, ∀ i < 2 * n, ∀ i' < 2 * n, i ≠ i' → er n i ≠ er n i' := by decide

theorem er_regs : ∀ n ≤ 4, ∀ i < 2 * n,
    er n i ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x19] := by decide

theorem er_mem : ∀ n ≤ 4, ∀ i < 2 * n, er n i ∈ entryRegs n := by decide

theorem entryRegs_regs : ∀ n ≤ 4, ∀ r ∈ entryRegs n,
    r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x19] := by decide

/-- The words of an entry at `x16 + o`: each loaded into `x6` and kept in its
register by `csel` unless the carry is set. -/
theorem cselWords_ok {n : Nat} (hn : n ≤ 4) {o : Nat} (ho : o % 8 = 0) :
    ∀ k ≤ 2 * n, ∀ {s : State}, o + 8 * k ≤ 32768 →
      (∀ i < k, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (o + 8 * i)) 8) →
      WP isa (.block ((List.range k).flatMap fun i =>
          [.ldr .x .x6 .x16 (o + 8 * i), .csel .x (er n i) (er n i) .x6])) s fun t =>
        (∀ i < 2 * n, t.gpr (er n i) = if i < k ∧ s.c = false then
          s.mem.readW (s.gpr .x16 + BitVec.ofNat 64 (o + 8 * i)) 64 else s.gpr (er n i)) ∧
        t.c = s.c ∧ Keeps (.x6 :: entryRegs n) s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun i _ => by simp, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk, s, ho', hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (cselWords_ok hn ho k (by omega) (by omega) fun i hi => hr i (by omega))
      fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    have h16 : s₁.gpr .x16 = s.gpr .x16 := k₁.gpr _ (by
      simp only [List.mem_cons, not_or]
      exact ⟨by decide, fun h => entryRegs_regs n hn _ h (by simp)⟩)
    have hrk := hr k (by omega)
    rw [← h16, ← k₁.rd, ← k₁.wr] at hrk
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x (by omega) hrk, exec_csel,
      Option.some.injEq, exists_eq_left']
    have hne := er_regs n hn k (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
    refine ⟨fun i hi => ?_, by simp only [RegUpd.c_write]; exact c₁, ?_⟩
    · by_cases hik : i = k
      · subst hik
        have hx6 : ¬ er n i = .x6 := hne.2.2.2.2.2.2.1
        simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, State.read, RegUpd.c_write,
          RegUpd.gpr_write, hx6, ite_false, c₁, k₁.mem, h16, Nat.lt_add_one, true_and]
        rw [e₁ i hi]
        cases s.c <;> simp
      · rw [RegUpd.gpr_write_of_ne _ _ _ (er_ne n hn i hi k (by omega) hik),
          RegUpd.gpr_write_of_ne _ _ _ (fun h => (er_regs n hn i hi) (by rw [h]; simp)), e₁ i hi]
        by_cases hlt : i < k
        · simp [hlt, show i < k + 1 by omega]
        · simp [hlt, show ¬ i < k + 1 by omega]
    · refine k₁.trans ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      simp only [List.mem_cons, not_or] at hr
      rw [RegUpd.gpr_write_of_ne _ _ _ (fun h => hr.2 (by rw [h]; exact er_mem n hn k (by omega))),
        RegUpd.gpr_write_of_ne _ _ _ hr.1]

theorem xor_eq_zero_iff (x y : BitVec 64) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· ^^^ y) h
    simpa [BitVec.xor_assoc] using this
  · rintro rfl; exact BitVec.xor_self

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

/-- Entry `m` (from 1): `x1 = m`, and each word kept in its register unless
`m` is the magnitude `a` in `x2`, when it is the entry's word. -/
theorem selEntry_ok (K : TCombCfg) (hn : K.M.n ≤ 4) {s : State} {a m : Nat} (hm : 1 ≤ m)
    (ha : a < 2 ^ 64) (hm' : m < 2 ^ 64) (hx1 : s.gpr .x1 = BitVec.ofNat 64 (m - 1))
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 a) (hx5 : s.gpr .x5 = 1)
    (ho : 16 * K.M.n * (m - 1) + 8 * (2 * K.M.n) ≤ 32768)
    (hr : ∀ i < 2 * K.M.n,
      InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * K.M.n * (m - 1) + 8 * i)) 8) :
    WP isa (.block (K.selEntry m)) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 m ∧
      (∀ i < 2 * K.M.n, t.gpr (er K.M.n i) = if a = m then
        s.mem.readW (s.gpr .x16 + BitVec.ofNat 64 (16 * K.M.n * (m - 1) + 8 * i)) 64
        else s.gpr (er K.M.n i)) ∧
      Keeps (.x1 :: .x3 :: .x4 :: .x6 :: entryRegs K.M.n) s t := by
  rw [show K.selEntry m = ([.add .x .x1 .x1 .x5, .logic .eor .x .x3 .x2 .x1, .subs .x .x4 .x3 .x5] :
      List Instr) ++ (List.range (2 * K.M.n)).flatMap (fun i =>
        [.ldr .x .x6 .x16 (16 * K.M.n * (m - 1) + 8 * i), .csel .x (er K.M.n i) (er K.M.n i) .x6])
      from rfl, WP.block_append_iff]
  have hpre : WP isa (.block ([.add .x .x1 .x1 .x5, .logic .eor .x .x3 .x2 .x1,
      .subs .x .x4 .x3 .x5] : List Instr)) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 m ∧ t.c = decide (a ≠ m) ∧ Keeps [.x1, .x3, .x4] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq, ite_true, ite_false,
      reduceCtorEq, hx1, hx2, hx5, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat,
        show m - 1 + 1 = m by omega]
    · rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, carry_sub_one, BitVec.ofNat_add_ofNat,
        show m - 1 + 1 = m by omega]
      congr 1
      rw [ne_eq, xor_eq_zero_iff]
      exact propext ⟨fun h e => h (by rw [e]), fun h e => h (by
        have := congrArg BitVec.toNat e
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hm'] at this)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_addWithCarry, RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  refine WP.mono hpre fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  have h16 : s₁.gpr .x16 = s.gpr .x16 := k₁.gpr _ (by decide)
  refine WP.mono (cselWords_ok hn (o := 16 * K.M.n * (m - 1)) (by rw [Nat.mul_assoc]; omega)
    (2 * K.M.n) (Nat.le_refl _) (by omega) fun i hi => by rw [h16, k₁.rd, k₁.wr]; exact hr i hi)
    fun t ⟨et, ct, kt⟩ => ?_
  refine ⟨?_, fun i hi => ?_, (k₁.mono (by sub_regs)).trans (kt.mono (by sub_regs))⟩
  · rw [kt.gpr _ (by
      simp only [List.mem_cons, not_or]
      exact ⟨by decide, fun h => entryRegs_regs K.M.n hn _ h (by simp)⟩), e₁]
  · rw [et i hi, c₁, h16, k₁.mem, k₁.gpr _ (by
      have := er_regs K.M.n hn i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.1, this.2.2.2.1, this.2.2.2.2.1⟩)]
    by_cases h : a = m <;> simp [h, hi]

/-- The entries `1 … m`: `x1 = m`, and the registers hold entry `a`'s words if
`1 ≤ a ≤ m`, else what they held. -/
theorem entries_ok (K : TCombCfg) (hn : K.M.n ≤ 4) {a : Nat} (ha : a < 2 ^ 64) :
    ∀ m, m < 2 ^ 64 → 16 * K.M.n * m ≤ 32768 → ∀ {s : State}, s.gpr .x1 = 0 →
      s.gpr .x2 = BitVec.ofNat 64 a → s.gpr .x5 = 1 →
      (∀ e < m, ∀ i < 2 * K.M.n,
        InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * K.M.n * e + 8 * i)) 8) →
      WP isa (.block ((List.range m).flatMap fun e => K.selEntry (e + 1))) s fun t =>
        t.gpr .x1 = BitVec.ofNat 64 m ∧
        (∀ i < 2 * K.M.n, t.gpr (er K.M.n i) = if 1 ≤ a ∧ a ≤ m then
          s.mem.readW (s.gpr .x16 + BitVec.ofNat 64 (16 * K.M.n * (a - 1) + 8 * i)) 64
          else s.gpr (er K.M.n i)) ∧
        Keeps (.x1 :: .x3 :: .x4 :: .x6 :: entryRegs K.M.n) s t
  | 0, _, _, s, h1, _, _, _ => WP.block_nil ⟨h1, fun i _ => by simp; omega, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | m + 1, hm, hb, s, h1, h2, h5, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    have hb' : 16 * K.M.n * m + 16 * K.M.n ≤ 32768 := by rw [Nat.mul_succ] at hb; exact hb
    refine WP.mono (entries_ok K hn ha m (by omega) (by omega) h1 h2 h5 fun e he => hr e (by omega))
      fun s₁ ⟨e₁, v₁, k₁⟩ => ?_
    have hk : ∀ r ∈ [Reg.x2, .x5, .x16], s₁.gpr r = s.gpr r := fun r hr' => k₁.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl <;>
        simp only [List.mem_cons, not_or] <;>
        exact ⟨by decide, by decide, by decide, by decide, fun h => entryRegs_regs K.M.n hn _ h (by simp)⟩)
    refine WP.mono (selEntry_ok K hn (m := m + 1) (by omega) ha hm (by rw [e₁]; rfl)
      (by rw [hk _ (by simp)]; exact h2) (by rw [hk _ (by simp)]; exact h5)
      (by rw [Nat.add_sub_cancel]; omega)
      fun i hi => by rw [hk _ (by simp), k₁.rd, k₁.wr]; exact hr m (by omega) i hi)
      fun t ⟨et, vt, kt⟩ => ⟨et, fun i hi => ?_, k₁.trans kt⟩
    rw [vt i hi, hk _ (by simp), k₁.mem, v₁ i hi, Nat.add_sub_cancel]
    by_cases h : a = m + 1
    · subst h; simp
    · by_cases h' : 1 ≤ a ∧ a ≤ m
      · simp [h, h', show 1 ≤ a ∧ a ≤ m + 1 by omega]
      · simp [h, h', show ¬ (1 ≤ a ∧ a ≤ m + 1) by omega]

/-- Registers holding words of memory hold their number. -/
theorem regsVal_of_words {s : State} {m : Mem} {B : Addr} :
    ∀ (rs : List Reg) (o : Nat), (∀ i < rs.length, s.gpr (rs.getD i .x8) = word m B (o + 8 * i)) →
      regsVal s rs = wordsVal m B o rs.length
  | [], _, _ => rfl
  | r :: rs, o, h => by
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero] at h0
    simp only [regsVal, wordsVal, List.length_cons, h0]
    rw [regsVal_of_words rs (o + 8) fun i hi => by
      have := h (i + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at this
      rw [this, show o + 8 * (i + 1) = o + 8 + 8 * i by omega]]

/-- Registers holding the words of `v` hold `v`. -/
theorem regsVal_of_wordOf {s : State} :
    ∀ (rs : List Reg) (v : Nat), v < 2 ^ (64 * rs.length) →
      (∀ i < rs.length, s.gpr (rs.getD i .x8) = wordOf v i) → regsVal s rs = v
  | [], v, hv, _ => by simp at hv; simp [regsVal]; omega
  | r :: rs, v, hv, h => by
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, wordOf, Nat.mul_zero, Nat.shiftRight_zero] at h0
    simp only [List.length_cons] at hv
    have hv' : v < 2 ^ 64 * 2 ^ (64 * rs.length) := by
      rw [← Nat.pow_add, show 64 + 64 * rs.length = 64 * (rs.length + 1) by omega]; exact hv
    have ih := regsVal_of_wordOf rs (v / 2 ^ 64) (Nat.div_lt_of_lt_mul hv')
      fun i hi => by
        have := h (i + 1) (by simp; omega)
        simp only [List.getD_cons_succ, wordOf] at this
        rw [this, wordOf, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
          Nat.div_div_eq_div_mul, ← Nat.pow_add, show 64 + 64 * i = 64 * (i + 1) by omega]
    simp only [regsVal, h0, ih, BitVec.toNat_ofNat]
    omega

theorem getD_take {rs : List Reg} {n i : Nat} (hi : i < n) : (rs.take n).getD i .x8 = rs.getD i .x8 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true]

theorem getD_drop {rs : List Reg} {n i : Nat} : (rs.drop n).getD i .x8 = rs.getD (n + i) .x8 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The registers `rs` set to the words of `v`. -/
theorem setRegs_ok (s : State) {v : Nat} :
    ∀ (rs : List Reg) (k : Nat), k ≤ rs.length → rs.Nodup →
      WP isa (.block ((List.range k).flatMap fun i => const64 (rs.getD i .x8) (wordOf v i))) s fun t =>
        (∀ i < k, t.gpr (rs.getD i .x8) = wordOf v i) ∧ Keeps rs s t
  | _, 0, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | rs, k + 1, hk, hnd => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (setRegs_ok s rs k (by omega) hnd) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hmem : rs.getD k .x8 ∈ rs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
    refine WP.mono (const64_ok s₁ _ _) fun t ⟨et, kt⟩ => ⟨fun i hi => ?_,
      k₁.trans (kt.mono fun q hq => by simp only [List.mem_singleton] at hq; rw [hq]; exact hmem)⟩
    by_cases hik : i = k
    · rw [hik, et]
    · have hne : rs.getD i .x8 ≠ rs.getD k .x8 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
        simp only [Option.getD_some]
        exact fun h => hik ((hnd.getElem_inj).mp h)
      rw [kt.gpr _ (by simpa using hne), e₁ i (by omega)]

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

theorem entryRegs_take_getD {n i : Nat} (hi : i < n) :
    ((entryRegs n).take n).getD i .x8 = er n i := by
  rw [getD_take hi]; rfl

theorem entryRegs_drop_getD {n i : Nat} : ((entryRegs n).drop n).getD i .x8 = er n (n + i) := by
  rw [getD_drop]; rfl

theorem entryRegs_length : ∀ n ≤ 4, (entryRegs n).length = 2 * n := by decide

theorem entryRegs_nodup : ∀ n ≤ 4, (entryRegs n).Nodup := by decide

theorem er_take : ∀ n ≤ 4, ∀ i < n, er n i ∈ (entryRegs n).take n ∧ er n i ∉ (entryRegs n).drop n := by
  decide

theorem er_drop : ∀ n ≤ 4, ∀ i < n,
    er n (n + i) ∈ (entryRegs n).drop n ∧ er n (n + i) ∉ (entryRegs n).take n := by
  decide

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

/-- The entry of the magnitude `a ≤ H` of table `j = x19` into `E`, from the
tables at `T` (the static `tsym`'s address): its `x` and `y` if `a ≥ 1`, else
`(0 : R : 0)`; `Z` is `R` unless `a = 0`. -/
theorem tselect_ok (K : TCombCfg) (hn : K.M.n ≤ 4) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) {j a : Nat} {T : Addr} (hx19 : s.gpr .x19 = BitVec.ofNat 64 j)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 a) (ha : a ≤ K.H) (hH : 16 * K.M.n * K.H ≤ 32768)
    (htb : K.tblBytes < 65536) (hHlt : K.H < 2 ^ 64) (hT : s.syms K.tsym = T)
    (hE : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ size ∧ d % 8 = 0)
    (hap : (K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.x + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y))
    (hone : K.one < 2 ^ (64 * K.M.n))
    (hreg : ∀ e < K.H, ∀ i < 2 * K.M.n, InRegions (s.rd ++ s.wr)
      (T + BitVec.ofNat 64 (j * K.tblBytes) + BitVec.ofNat 64 (16 * K.M.n * e + 8 * i)) 8) :
    WP isa (.block K.select) s fun t =>
      wordsVal t.mem base K.E.x K.M.n = (if 1 ≤ a then
        wordsVal s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1)) K.M.n else 0) ∧
      wordsVal t.mem base K.E.y K.M.n = (if 1 ≤ a then
        wordsVal s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n
        else K.one) ∧
      wordsVal t.mem base K.E.z K.M.n = (if 1 ≤ a then K.one else 0) ∧
      KeepRegs (.x1 :: .x2 :: .x3 :: .x4 :: .x5 :: .x6 :: .x7 :: .x16 :: .x17 :: entryRegs K.M.n) s t ∧
      Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem := by
  have hnw := hs.nowrap
  have hlen := entryRegs_length _ hn
  have hnd := entryRegs_nodup _ hn
  have hEx := hE K.E.x (by simp)
  have hEy := hE K.E.y (by simp)
  have hEz := hE K.E.z (by simp)
  obtain ⟨axy, axz, ayz⟩ := hap
  have ha64 : a < 2 ^ 64 := by omega
  -- What every step keeps.
  have nE : ∀ r ∈ entryRegs K.M.n, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x5 ∧ r ≠ .x7 ∧ r ≠ .x16 :=
    fun r hr => by
      have := entryRegs_regs _ hn r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2.2.1,
        this.2.2.2.2.2.2.2.2.1⟩
  have htake : ∀ r ∈ (entryRegs K.M.n).take K.M.n, r ∈ entryRegs K.M.n := fun r h => List.mem_of_mem_take h
  have hdrop : ∀ r ∈ (entryRegs K.M.n).drop K.M.n, r ∈ entryRegs K.M.n := fun r h => List.mem_of_mem_drop h
  simp only [TCombCfg.select, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selSetup_ok K hx19 hT htb) fun s₁ ⟨e16, e7, e5, e1, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h2₁ : s₁.gpr .x2 = BitVec.ofNat 64 a := by rw [k₁.gpr _ (by decide), hx2]
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok s₁ _) fun s₂ ⟨z₂, k₂⟩ => ?_
  have k₂' : ∀ r, r ∉ entryRegs K.M.n → s₂.gpr r = s₁.gpr r := fun r hr =>
    k₂.gpr r fun h => hr (htake r h)
  rw [WP.block_append_iff]
  refine WP.mono (setRegs_ok s₂ (v := K.one) ((entryRegs K.M.n).drop K.M.n) _ (Nat.le_refl _)
    (hnd.sublist (List.drop_sublist _ _))) fun s₃ ⟨z₃, k₃⟩ => ?_
  have k₃' : ∀ r, r ∉ entryRegs K.M.n → s₃.gpr r = s₂.gpr r := fun r hr =>
    k₃.gpr r fun h => hr (hdrop r h)
  have hm₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
  have hrd₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]
  have g : ∀ r ∈ [Reg.x1, .x2, .x5, .x16, .x7], s₃.gpr r = s₁.gpr r := fun r hr => by
    rw [k₃' r ?_, k₂' r ?_] <;>
    · intro h; have := nE r h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp at this
  -- Every entry.
  rw [WP.block_append_iff]
  refine WP.mono (entries_ok K hn ha64 K.H hHlt hH (s := s₃) (by rw [g _ (by simp), e1])
    (by rw [g _ (by simp), h2₁]) (by rw [g _ (by simp), e5])
    fun e he i hi => by rw [g _ (by simp), e16, hrd₃]; exact hreg e he i hi)
    fun s₄ ⟨e1₄, v₄, k₄⟩ => ?_
  have hm₄ : s₄.mem = s.mem := by rw [k₄.mem, hm₃]
  -- The registers' values before the entries.
  have r0 : ∀ i < K.M.n, s₃.gpr (er K.M.n i) = 0 := fun i hi => by
    rw [k₃.gpr _ (er_take _ hn i hi).2]; exact z₂ _ (er_take _ hn i hi).1
  have r1 : ∀ i < K.M.n, s₃.gpr (er K.M.n (K.M.n + i)) = wordOf K.one i := fun i hi => by
    have := z₃ i (by rw [List.length_drop, hlen]; omega)
    rwa [entryRegs_drop_getD] at this
  -- After the entries.
  have h16₃ : s₃.gpr .x16 = (T + BitVec.ofNat 64 (j * K.tblBytes)) := by rw [g _ (by simp), e16]
  have vx : ∀ i < K.M.n, s₄.gpr (er K.M.n i) =
      if 1 ≤ a then word s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * i) else 0 := fun i hi => by
    rw [v₄ i (by omega), h16₃, hm₃, r0 i hi]
    by_cases h : 1 ≤ a <;> simp [h, show a ≤ K.H from ha]
  have vy : ∀ i < K.M.n, s₄.gpr (er K.M.n (K.M.n + i)) =
      if 1 ≤ a then word s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i) else wordOf K.one i :=
    fun i hi => by
      rw [v₄ _ (by omega), h16₃, hm₃, r1 i hi,
        show 16 * K.M.n * (a - 1) + 8 * (K.M.n + i) = 16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i by omega]
      by_cases h : 1 ≤ a <;> simp [h, show a ≤ K.H from ha]
  have hlt := (List.length_take (l := entryRegs K.M.n) (i := K.M.n))
  have tlen : ((entryRegs K.M.n).take K.M.n).length = K.M.n := by rw [List.length_take, hlen]; omega
  have dlen : ((entryRegs K.M.n).drop K.M.n).length = K.M.n := by rw [List.length_drop, hlen]; omega
  have RX : regsVal s₄ ((entryRegs K.M.n).take K.M.n) = if 1 ≤ a then
      wordsVal s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1)) K.M.n else 0 := by
    by_cases h : 1 ≤ a
    · simp only [h, ↓reduceIte]
      refine (regsVal_of_words _ _ fun i hi => ?_).trans (by rw [tlen])
      rw [tlen] at hi; rw [entryRegs_take_getD hi, vx i hi]; simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]
      exact regsVal_of_wordOf _ 0 (Nat.two_pow_pos _) fun i hi => by
        rw [tlen] at hi; rw [entryRegs_take_getD hi, vx i hi, wordOf_zero]; simp only [h, ↓reduceIte]
  have RY : regsVal s₄ ((entryRegs K.M.n).drop K.M.n) = if 1 ≤ a then
      wordsVal s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n
      else K.one := by
    by_cases h : 1 ≤ a
    · simp only [h, ↓reduceIte]
      refine (regsVal_of_words _ _ fun i hi => ?_).trans (by rw [dlen])
      rw [dlen] at hi; rw [entryRegs_drop_getD, vy i hi]; simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]
      exact regsVal_of_wordOf _ _ (by rw [dlen]; exact hone) fun i hi => by
        rw [dlen] at hi; rw [entryRegs_drop_getD, vy i hi]; simp only [h, ↓reduceIte]
  -- The stores.
  have hs₃ : Scr s₃ base size := (hs₁.of_keeps k₂ (fun h => (nE _ (htake _ h)).1 rfl)).of_keeps k₃
    (fun h => (nE _ (hdrop _ h)).1 rfl)
  have hs₄ := hs₃.of_keeps k₄ (by
    intro h; simp only [List.mem_cons] at h
    rcases h with h | h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (nE _ h).1 rfl)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok _ hs₄ (o := K.E.x) (by rw [tlen]; exact hEx.1) hEx.2
    (hnd.sublist (List.take_sublist _ _))) fun s₅ ⟨w₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok _ hs₅ (o := K.E.y) (by rw [dlen]; exact hEy.1) hEy.2
    (hnd.sublist (List.drop_sublist _ _))) fun s₆ ⟨w₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  -- What the entries keep.
  have g₄ : ∀ r ∈ [Reg.x2, .x5, .x7], s₆.gpr r = s₁.gpr r := fun r hr => by
    rw [k₆.gpr r (by simp), k₅.gpr r (by simp), k₄.gpr r ?_, g r ?_]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp
    · intro h; simp only [List.mem_cons] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rcases h with h | h | h | h | h <;>
        first | exact absurd h (by decide) | exact (nE _ h).2.2.1 rfl | exact (nE _ h).2.2.2.1 rfl |
          exact (nE _ h).2.2.2.2.1 rfl
  -- `Z`.
  rw [TCombCfg.selZ, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (selZ_carry s₆ ha64 (by rw [g₄ _ (by simp), h2₁]) (by rw [g₄ _ (by simp), e5]))
    fun s₇ ⟨c₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  refine WP.mono (zWords_ok K hs₇ (by rw [k₇.gpr _ (by decide), g₄ _ (by simp), e7]) hEz.1 hEz.2
    K.M.n (Nat.le_refl _)) fun t ⟨wt, _, kt, Ot⟩ => ?_
  have hm₇ : s₇.mem = s₆.mem := k₇.mem
  rw [dlen] at O₆
  rw [tlen] at O₅
  have b64 : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ 2 ^ 64 := fun d hd => by
    have := (hE d hd).1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Ot.wordsVal axz (b64 _ (by simp)), hm₇, O₆.wordsVal axy (b64 _ (by simp)), ← RX, ← w₅, tlen]
  · rw [Ot.wordsVal ayz (b64 _ (by simp)), hm₇, ← RY, ← regsVal_congr fun q _ => k₅.gpr q (by simp),
      ← w₆, dlen]
  · refine wordsVal_of_shifts _ _ _ _ _ (by split <;> [exact hone; exact Nat.two_pow_pos _])
      fun i hi => ?_
    rw [wt i hi, c₇]
    by_cases h : 1 ≤ a <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> [rfl; simp]
  · refine (((((((Keeps.regs k₁).mono (by sub_regs)).trans ((Keeps.regs k₂).mono fun q hq => ?_)).trans
      ((Keeps.regs k₃).mono fun q hq => ?_)).trans ((Keeps.regs k₄).mono (by sub_regs))).trans
      ((k₅.trans k₆).mono fun _ h => absurd h List.not_mem_nil)).trans
      ((Keeps.regs k₇).mono (by sub_regs))).trans (kt.mono (by sub_regs))
    · simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (htake q hq)))))))))
    · simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (hdrop q hq)))))))))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [Ot x (by omega), hm₇, O₆ x (by omega), O₅ x (by omega), hm₄]


end VG.Proof.Weierstrass.AArch64
