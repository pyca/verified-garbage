module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Area
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Sel
import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSA with AVX512_IFMA on x86-64, any size: the table

`copyN o a` copies the numbers at `a` to `o` in
both regions (`copyN_ok`); `convTab` puts `Y` and `X` into Montgomery form
for `R = 2^(208 R)` (times `K1 ≡ 2^(416 R - 64 W)`, as they hold `2^(64 W)`
and `x 2^(64 W)`; entries 0 and 1, `conv0_ok`, `conv1_ok`), then writes the
table of the powers of `x` in the same loop (`tabIter_ok`, `convTab_ok`):
`T_0 = Y`, `T_1 = X` and `T_i = T_(i-1) X / 2^(208 R)`, so `T_i ≡ x^i 2^(208 R)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (wrList writeW256_outside word_wrList_unique readW256_outside off_add se_ofNat
  mont_mul2 mont_into0 mont_into1)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The offsets of a region, in `NB`, the table's `T NB` and `XE`. -/
theorem lay_offs (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : l.oK0 = l.NB ∧ l.oY = l.NB + 32 ∧ l.oX = 2 * l.NB + 32 ∧ l.oS = 3 * l.NB + 32 ∧
    l.oTab = 4 * l.NB + 32 ∧ l.oE = 4 * l.NB + 32 + l.T * l.NB ∧ l.oK1 = 4 * l.NB + 32 + l.T * l.NB + l.XE ∧
    l.oV = 5 * l.NB + 32 + l.T * l.NB + l.XE ∧ l.oFin = 5 * l.NB + 64 + l.T * l.NB + l.XE ∧
    l.D = 6 * l.NB + 64 + l.T * l.NB + l.XE := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Lay.D, Lay.oFin, Lay.oV, Lay.oK1, Lay.oE, Lay.oTab, Lay.oS, Lay.oX, Lay.oY, Lay.oK0] <;> omega_using []

/-- Entry `i` of the table ends within it. -/
theorem tab_le (hl : LayOk l) {i : Nat} (hi : i < l.T) : l.NB * i + l.NB ≤ l.T * l.NB := by
  have := hl.T_bounds
  rw [Nat.mul_comm l.T, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-- An entry below 16 is in the table, and not its last. -/
theorem T_gt (hl : LayOk l) {i : Nat} (h : i < 16) : i < l.T := by have := hl.T_bounds; omega

theorem dec_T (hl : LayOk l) {i : Nat} (h : i + 1 < 16) : decide (i + 1 = l.T) = false := by
  have := hl.T_bounds; exact decide_eq_false (by omega)

/-- Entries of the table at the same offset are the same. -/
theorem nb_mul_inj (hl : LayOk l) {i j : Nat} (h : l.NB * i = l.NB * j) : i = j := by
  have : 0 < l.NB := by rcases hl with rfl | rfl | rfl <;> decide
  exact Nat.eq_of_mul_eq_mul_left this h

theorem vy_setVy_self (s : State) (d : VReg) (v : BitVec 256) : (s.setVy d v).vy d = v := by
  cases d with
  | lo d => simp only [State.vy, State.setVy, State.ymm, State.setV, ite_true, StraightY.split_eq]
  | hi d => simp only [State.vy, State.setVy, ite_true]

/-- 32-byte copies at `rbx` plus offsets, from `x.1` to `x.2`, through register 0. -/
def copyCode (xs : List (Nat × Nat)) : List Instr :=
  xs.flatMap fun x => [.evLoad (vreg 0) (at_ .rbx x.1), .evStore (at_ .rbx x.2) (vreg 0)]

theorem copies_ok (hl : LayOk l) {B : Addr} :
    ∀ (xs : List (Nat × Nat)) (s : State), s.gpr .rbx = B → Scr s B (2 * l.D) →
      (∀ x ∈ xs, x.1 + 32 ≤ 2 * l.D ∧ x.2 + 32 ≤ 2 * l.D) →
      (∀ x ∈ xs, ∀ y ∈ xs, y.1 + 32 ≤ x.2 ∨ x.2 + 32 ≤ y.1) →
      WP isa (.block (copyCode xs)) s fun s' =>
        s'.mem = wrList s.mem B (xs.map fun x => (x.2, s.mem.readW (off B x.1) 256)) ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | [], s, _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | (a, o) :: rest, s, hB, hs, hxs, hsep => by
    have hD := hl.D_bounds
    have ho := hxs (a, o) (List.mem_cons_self ..)
    have hn := hs.nowrap
    rw [copyCode, List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append, WP.block_cons_iff]
    have hld : InRegions (s.rd ++ s.wr) (off B a) 32 :=
      let ⟨_, h, c⟩ := hs.region (d := a) (n := 32) (by omega_using [ho]) (by decide); ⟨_, List.mem_append_right _ h, c⟩
    have hst : InRegions s.wr (off B o) 32 :=
      let ⟨_, h, c⟩ := hs.region (d := o) (n := 32) (by omega_using [ho]) (by decide); ⟨_, h, c⟩
    refine ⟨s.setVy (vreg 0) (s.mem.readW (off B a) 256),
      by simp only [exec, ea_rG hB, State.load256, hld, ite_true, Option.map_some], ?_⟩
    have y₁ := vy_setVy_self s (vreg 0) (s.mem.readW (off B a) 256)
    have e₁ : ∀ t : State, t = s.setVy (vreg 0) (s.mem.readW (off B a) 256) →
        t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
      rintro t rfl; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    generalize hs₁ : s.setVy (vreg 0) (s.mem.readW (off B a) 256) = s₁ at y₁ ⊢
    obtain ⟨g₁, m₁, rd₁, wr₁, x₁⟩ := e₁ s₁ hs₁.symm
    have hB₁ : s₁.gpr .rbx = B := by rw [g₁]; exact hB
    rw [WP.block_cons_iff]
    refine ⟨{ s₁ with mem := s₁.mem.writeW (off B o) (s₁.vy (vreg 0)) }, by
      simp only [exec, ea_rG hB₁, State.store256, wr₁, hst, ite_true], ?_⟩
    rw [y₁, m₁]
    refine WP.mono (copies_ok hl rest _ (by rw [← g₁] at hB; exact hB) (hs.congr wr₁)
      (fun x hx => hxs x (List.mem_cons_of_mem _ hx))
      (fun x hx y hy => hsep x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)))
      fun s' ⟨m', g', rd', wr', x'⟩ => ⟨?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁, x'.trans x₁⟩
    rw [m', List.map_cons, wrList]
    refine congrArg (wrList _ B) (List.map_congr_left fun y hy => ?_)
    have := hxs y (List.mem_cons_of_mem _ hy)
    have hs' := hsep (a, o) (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy)
    exact congrArg _ (readW256_outside (writeW256_outside _ B _ (by omega_arith)) (by omega_using [hs']) (by omega_using [hn, this]))

/-- The copies of `copyN o a`. -/
def cpList (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (o a : Nat) : List (Nat × Nat) :=
  (List.range 2).flatMap fun p => (List.range l.R).map fun k => (l.D * p + a + 32 * k, l.D * p + o + 32 * k)

theorem copyN_eq (o a : Nat) : copyN l o a = copyCode (cpList l o a) := by
  simp only [copyN, copyCode, cpList, List.flatMap_assoc, List.flatMap_map]

theorem mem_cpList {o a : Nat} {x : Nat × Nat} (h : x ∈ cpList l o a) :
    ∃ p < 2, ∃ k < l.R, x = (l.D * p + a + 32 * k, l.D * p + o + 32 * k) := by
  simp only [cpList, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨p, hp, k, hk, rfl⟩ := h
  exact ⟨p, hp, k, hk, rfl⟩

/-- `[o] := [a]` in both regions. -/
theorem copyN_ok (hl : LayOk l) {s : State} {B : Addr} {o a : Nat} (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * l.D)) (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hoa : a + l.NB ≤ o ∨ o + l.NB ≤ a) :
    WP isa (.block (copyN l o a)) s fun s' =>
      (∀ p < 2, ∀ q < l.L, limb l s'.mem B (l.D * p + o) q = limb l s.mem B (l.D * p + a) q) ∧
      Out2 l B o l.NB s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, _⟩ := hl.bounds
  have hD := hl.D_bounds
  have hNB : l.NB = 32 * l.R := rfl
  rw [copyN_eq]
  refine WP.mono (copies_ok hl _ s hB hs (fun x hx => ?_) (fun x hx y hy => ?_))
    fun s' ⟨hm, hg, hrd, hwr, hx⟩ => ⟨fun p hp q hq => ?_, ?_, hg, hrd, hwr, hx⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := mem_cpList hx
    rcases D_mul (l := l) hp with h | h <;> dsimp only <;> omega_using [ho, ha, hNB, hk, h]
  · obtain ⟨p, hp, k, hk, rfl⟩ := mem_cpList hx
    obtain ⟨p', hp', k', hk', rfl⟩ := mem_cpList hy
    rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl <;> rcases (by omega_using [hp'] : p' = 0 ∨ p' = 1) with rfl | rfl <;>
          dsimp only <;> simp only [Nat.mul_zero, Nat.mul_one] <;> omega_using [hoa, hNB, hk, hk', ho, ha]
  · have hk : q % l.R < l.R := Nat.mod_lt _ (by omega_using [hR])
    have ht : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    have e := word_wrList_unique B (e := l.D * p + o + 32 * (q % l.R)) (t := q / l.R)
      (v := s.mem.readW (off B (l.D * p + a + 32 * (q % l.R))) 256) ht
      (by rcases D_mul (l := l) hp with h | h <;> omega_using [ho, hD, hNB, hk, h])
      ((cpList l o a).map fun x => (x.2, s.mem.readW (off B x.1) 256)) s.mem
      (List.mem_map.2 ⟨(l.D * p + a + 32 * (q % l.R), l.D * p + o + 32 * (q % l.R)),
        by simp only [cpList, List.mem_flatMap, List.mem_map, List.mem_range]; exact ⟨p, hp, q % l.R, hk, rfl⟩, rfl⟩)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p', hp', k', hk', rfl⟩ := mem_cpList hy
        rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl <;> rcases (by omega_using [hp'] : p' = 0 ∨ p' = 1) with rfl | rfl <;>
          dsimp only <;> simp only [Nat.mul_zero, Nat.mul_one] <;> omega_using [ho, hD, hNB, hk', hk])
      (fun x hx he => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p', hp', k', hk', rfl⟩ := mem_cpList hy
        dsimp only at he ⊢
        have : p' = p ∧ k' = q % l.R := by
          rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl <;> rcases (by omega_using [hp'] : p' = 0 ∨ p' = 1) with rfl | rfl <;>
            simp only [Nat.mul_zero, Nat.mul_one] at he <;> omega_using [he, hD, hNB, hk, hk']
        rw [this.1, this.2])
    show (word s'.mem B _).toNat = (word s.mem B _).toNat
    have ex := readW_extract s.mem (off B (l.D * p + a + 32 * (q % l.R))) (w := 256) (k := 8 * (q / l.R)) (n := 8)
      (by omega_using [ht])
    rw [hm, show l.D * p + o + l.off q = l.D * p + o + 32 * (q % l.R) + 8 * (q / l.R) by unfold Lay.off; omega_using [], e,
      show 64 * (q / l.R) = 8 * (8 * (q / l.R)) by omega_using []]
    refine congrArg BitVec.toNat (ex.trans ?_)
    rw [off_add]
    exact congrArg (fun d => s.mem.readW (off B d) 64) (by unfold Lay.off; omega_using [])
  · rw [hm]
    exact wrList_out2 B (by omega_using [ho, hD]) _ s.mem fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨p, hp, k, hk, rfl⟩ := mem_cpList hy
      exact ⟨p, hp, by dsimp only; omega_using [], by dsimp only; omega_using [hNB, hk]⟩

theorem NB_le (hl : LayOk l) : l.NB ≤ 320 ∧ 160 ≤ l.NB := by
  rcases hl with rfl | rfl | rfl <;> decide

theorem dbl_le (hl : LayOk l) : 64 * l.W ≤ 104 * l.S := by rcases hl with rfl | rfl | rfl <;> decide

/-! ## The pieces of `convTabBody` -/

/-- `cmp r13, k`. -/
theorem cmp13_ok (s : State) {n k : Nat} (h13 : s.gpr .r13 = BitVec.ofNat 64 n) (hn : n < 2 ^ 31) (hk : k < 2 ^ 31) :
    WP isa (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.zf = some (decide (n = k)) ∧ t.cf = some (decide (n < k)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  xrun [h13, se_ofNat hk]
  refine ⟨ofNat_sub_beq (j := n) (N := k) (by omega) (by omega), ?_, rfl⟩
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]

/-- The operands of entry `i < 2`: `Y` or `X`, in place, and `K1`. -/
theorem convSetup_ok (hl : LayOk l) {s : State} {B : Addr} {i : Nat}
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.block (convSetup l)) s fun s' =>
      s'.gpr .r8 = off B (l.oY + l.NB * i) ∧ s'.gpr .r9 = off B l.oK1 ∧
      s'.gpr .r11 = off B (l.oY + l.NB * i) ∧
      VG.Proof.MlKem.X86_64.Keep [.r8, .r9, .r11] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have e : off B (l.oY + l.NB * i) = B + BitVec.ofNat 64 (l.oTab + l.NB * i) - BitVec.ofNat 64 (l.oTab - l.oY) := by
    rw [VG.Offset.add_ofNat_sub _ (by omega_using [o2, o5])]
    exact congrArg (off B) (by omega_using [o2, o5])
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .r9, .r11] (Q := fun s' =>
    s'.gpr .r8 = off B (l.oY + l.NB * i) ∧ s'.gpr .r9 = off B l.oK1 ∧
      s'.gpr .r11 = off B (l.oY + l.NB * i) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) (by
    xrun [convSetup, hB, h13, se_ofNat (show l.oTab - l.oY < 2 ^ 31 by omega_using [hD, o2, o5]),
      se_ofNat (show l.oK1 < 2 ^ 31 by omega_using [hD, o7, o10])]
    exact ⟨e.symm, e.symm, rfl⟩) rfl)
    fun s' ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, k, d, e⟩

/-- The operands of entry `i ≥ 1` of the table: `T_(i-1)`, `X`, `T_i`. -/
theorem tabHead_ok (hl : LayOk l) {s : State} {B : Addr} {i : Nat} (hi : 1 ≤ i) (_hi' : i < l.T)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.block (tabSetup l)) s fun s' =>
      s'.gpr .r8 = off B (l.oTab + l.NB * (i - 1)) ∧ s'.gpr .r9 = off B l.oX ∧
      s'.gpr .r11 = off B (l.oTab + l.NB * i) ∧
      VG.Proof.MlKem.X86_64.Keep [.r8, .r9, .r11] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNi : l.NB ≤ l.NB * i := Nat.le_mul_of_pos_right _ (by omega_using [hi])
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .r9, .r11] (Q := fun s' =>
    s'.gpr .r8 = off B (l.oTab + l.NB * (i - 1)) ∧ s'.gpr .r9 = off B l.oX ∧
      s'.gpr .r11 = off B (l.oTab + l.NB * i) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) (by
    xrun [tabSetup, hB, h13, se_ofNat (show l.NB < 2 ^ 31 by omega_using [hD]), se_ofNat (show l.oX < 2 ^ 31 by omega_using [hD, o3])]
    and_intros
    any_goals rfl
    · rw [VG.Offset.add_ofNat_sub _ (by omega_using [hNi])]
      exact congrArg (off B) (by rw [Nat.mul_sub_one]; omega_using [hNi])) rfl)
    fun s' ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, k, d, e⟩

/-- The next entry, `ZF` after the last. -/
theorem tabTail_ok (hl : LayOk l) {s : State} {i : Nat} (hi : i < l.T)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
        .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.T * l.NB)))]) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * (i + 1)) ∧ s'.zf = some (decide (i + 1 = l.T)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNi : l.NB * i + l.NB ≤ l.T * l.NB := tab_le hl hi
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun s' =>
    s'.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * (i + 1)) ∧ s'.zf = some (decide (i + 1 = l.T)) ∧
      s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) (by
    xrun [h13, se_ofNat (show l.NB < 2 ^ 31 by omega_using [hD]),
      se_ofNat (show l.oTab + l.T * l.NB < 2 ^ 31 by omega_using [hD, o5, o10])]
    and_intros
    · rw [← BitVec.ofNat_add]; congr 1; rw [Nat.mul_succ]; omega_using []
    · rw [← BitVec.ofNat_add, ofNat_sub_beq (by omega_using [hD, o5, o10, hNi]) (by omega_using [hD, o5, o10])]
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
      · exact nb_mul_inj hl (by rw [Nat.mul_succ, Nat.mul_comm l.NB l.T]; omega_using [h])
      · rw [← h, Nat.succ_mul, Nat.mul_comm i]; omega_using []
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

/-- A state that differs from `s` only in the flags. -/
def Flags (s t : State) : Prop := t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr

theorem Flags.keep {s t : State} (h : Flags s t) (rs : List Reg) : VG.Proof.MlKem.X86_64.Keep rs s t :=
  ⟨fun r _ => by rw [h.1], h.2.2.1, h.2.2.2.1⟩

/-- The head of entry `i`: the conversion's operands below 2, the table's
from 2. -/
theorem bodyHead_ok (hl : LayOk l) {s : State} {i : Nat} (hi : i < l.T) {R : Prog isa} {Q : State → Prop}
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i))
    (hc : i < 2 → ∀ t, Flags s t → WP isa (.block (convSetup l)) t fun u => WP isa R u Q)
    (ht : 2 ≤ i → ∀ t, Flags s t → WP isa (.block (tabSetup l)) t fun u => WP isa R u Q) :
    WP isa (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + 2 * l.NB)))])
      (.seq (.ite .b (.block (convSetup l)) (.block (tabSetup l))) R)) s Q := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNi : l.NB * i + l.NB ≤ l.T * l.NB := tab_le hl hi
  refine WP.seq (WP.mono (cmp13_ok s h13 (by omega_using [hD, o5, o10, hNi]) (by omega_using [hD, o5, o10]))
    fun t ⟨_, hcf, hg, hm, hrd, hwr, hx⟩ => ?_)
  have hf : Flags s t := ⟨hg, hm, hrd, hwr, hx⟩
  have e : decide (l.oTab + l.NB * i < l.oTab + 2 * l.NB) = decide (i < 2) := by
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · by_contra h'
      have := Nat.mul_le_mul_left l.NB (show 2 ≤ i by omega_using [h'])
      omega_using [h, this]
    · have := Nat.mul_le_mul_left l.NB (show i ≤ 1 by omega_using [h])
      have := NB_le hl
      omega_arith
  rw [e] at hcf
  refine WP.seq (WP.ite (decide (i < 2)) hcf (fun h => hc (by simpa using h) t hf) (fun h => ht ?_ t hf))
  simp only [decide_eq_false_iff_not] at h
  omega_using [h]

/-- The end of entry `i ≠ 1`: no copies, then the next entry. -/
theorem bodyTail_ok (hl : LayOk l) {s : State} {i : Nat} (hi : i < l.T) (h1 : i ≠ 1)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.NB)))])
      (.seq (.ite .e (.block (copyN l l.oTab l.oY ++ copyN l (l.oTab + l.NB) l.oX)) (.block []))
        (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
          .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.T * l.NB)))]))) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * (i + 1)) ∧ s'.zf = some (decide (i + 1 = l.T)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNi : l.NB * i + l.NB ≤ l.T * l.NB := tab_le hl hi
  refine WP.seq (WP.mono (cmp13_ok s h13 (by omega_using [hD, o5, o10, hNi]) (by omega_using [hD, o5, o10]))
    fun t ⟨hz, _, hg, hm, hrd, hwr, hx⟩ => ?_)
  have hne : l.oTab + l.NB * i ≠ l.oTab + l.NB := fun h => h1 (by
    have := NB_le hl
    exact Nat.eq_of_mul_eq_mul_left (show 0 < l.NB by omega_using [this]) (by rw [Nat.mul_one]; omega_using [h]))
  rw [decide_eq_false hne] at hz
  refine WP.seq (WP.ite false hz (fun h => by cases h) fun _ => WP.block_nil ?_)
  refine WP.mono (tabTail_ok hl hi (by rw [hg]; exact h13)) fun u ⟨a, b, k, c, d⟩ =>
    ⟨a, b, ⟨fun r hr => by rw [k.gpr hr, hg], by rw [k.2.1, hrd], by rw [k.2.2, hwr]⟩, by rw [c, hm], by rw [d, hx]⟩

/-! ## The loop -/

/-- After the entries below `i ≥ 2` of the table, from `s₀`: `Y` and `X` in
Montgomery form, and the table. -/
structure TabInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (i : Nat) (t : State) : Prop where
  rbx : t.gpr .rbx = B
  r13 : t.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)
  scr : Scr t B (2 * l.D)
  ar : Ar l t.mem B M k
  tab : ∀ j < i, ∀ p < 2, Good l t.mem B M (l.oTab + l.NB * j) p ∧
    (Q → val52 l t.mem B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.S) % M p)
  yg : ∀ p < 2, Good l t.mem B M l.oY p
  yv : Q → ∀ p < 2, val52 l t.mem B (l.D * p + l.oY) % M p = x p ^ 0 * 2 ^ (52 * l.S) % M p
  xg : ∀ p < 2, Good l t.mem B M l.oX p
  xv : Q → ∀ p < 2, val52 l t.mem B (l.D * p + l.oX) % M p = x p ^ 1 * 2 ^ (52 * l.S) % M p
  frame : Out2 l B l.oY (l.oTab + l.T * l.NB - l.oY) s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r13 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- Entry `i ≥ 2` of the table. -/
theorem tabIter_ok (hl : LayOk l) {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {i : Nat}
    (hi : 2 ≤ i) (hi' : i < l.T) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : TabInv l s₀ B M k x Q i t) :
    WP isa (convTabBody l) t fun t' => TabInv l s₀ B M k x Q (i + 1) t' ∧ t'.zf = some (decide (i + 1 = l.T)) := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNi : l.NB * i + l.NB ≤ l.T * l.NB := tab_le hl hi'
  have hNi1 : l.NB * (i - 1) + l.NB = l.NB * i := by
    rw [← Nat.mul_succ, show (i - 1).succ = i by omega_using [hi]]
  unfold convTabBody
  refine bodyHead_ok hl hi' h.r13 (fun h' => absurd h' (by omega_using [hi])) fun _ t₀ hf => ?_
  have hB₀ : t₀.gpr .rbx = B := by rw [hf.1]; exact h.rbx
  have h13₀ : t₀.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i) := by rw [hf.1]; exact h.r13
  refine WP.mono (tabHead_ok hl (by omega_using [hi]) hi' hB₀ h13₀) fun t₁ ⟨h8, h9, h11, k₁, me₁, mx₁⟩ => ?_
  rw [hf.2.1] at me₁
  have rbx₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB₀
  have hg : ∀ p < 2, Good l t₁.mem B M (l.oTab + l.NB * (i - 1)) p := fun p hp => by
    rw [me₁]; exact (h.tab (i - 1) (by omega_using [hi]) p hp).1
  refine WP.seq (WP.mono (ammCore2_ok hl (o := l.oTab + l.NB * i) (k := k) rbx₁ h8 h9 h11
    (h.scr.congr (by rw [k₁.2.2, hf.2.2.2.1]))
    (by rw [me₁]; exact h.ar) (by omega_using [o5, o10, hNi]) (by omega_using [o2, o5])
        (by omega_using [o5, o10, hNi, hNi1]) (by omega_using [o3, o10]) hg
    (fun p hp => by rw [me₁]; exact h.xg p hp))
    fun t₂ ⟨hv₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁.gpr (by decide)]; exact h13₀
  refine WP.mono (bodyTail_ok hl hi' (by omega_using [hi]) r13₂) fun t₃ ⟨r13₃, z₃, k₃, me₃, mx₃⟩ => ⟨⟨?_, r13₃, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₃⟩
  · rw [k₃.gpr (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact rbx₁
  · exact h.scr.congr (by rw [k₃.2.2, wr₂, k₁.2.2, hf.2.2.2.1])
  · rw [me₃]; exact ar₂
  · have hoD : l.oTab + l.NB * i + l.NB ≤ l.D := by omega_using [o5, o10, hNi]
    intro j hj p hp
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
    · have hNj : l.NB * j + l.NB ≤ l.NB * i := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      have hc : l.oTab + l.NB * j + l.NB ≤ l.oTab + l.NB * i ∨ l.oTab + l.NB * i + l.NB ≤ l.oTab + l.NB * j :=
        .inl (by omega_using [hNj])
      have hcD : l.oTab + l.NB * j + l.NB ≤ l.D := by omega_using [hoD, hNj]
      obtain ⟨g, v⟩ := h.tab j hj p hp
      refine ⟨?_, fun hq => ?_⟩
      · have g₁ : Good l t₁.mem B M (l.oTab + l.NB * j) p := by rw [me₁]; exact g
        rw [me₃]; exact g₁.of_out2 hl hp f₂ hc hcD hoD
      · rw [me₃, f₂.val hl hp hc hcD hoD, me₁]; exact v hq
    · obtain ⟨g, v⟩ := hv₂ p hp
      refine ⟨by rw [me₃]; exact g, fun hq => ?_⟩
      rw [me₁] at v
      have e := mont_mul2 (R := 2 ^ (52 * l.S)) (hR p hp) ((h.tab (j - 1) (by omega_using [hi]) p hp).2 hq) (h.xv hq p hp) v
      rw [show j - 1 + 1 = j by omega_using [hi]] at e
      rw [me₃]; exact e
  · intro p hp
    rw [me₃]
    have g₁ : Good l t₁.mem B M l.oY p := by rw [me₁]; exact h.yg p hp
    exact g₁.of_out2 hl hp f₂ (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]) (by omega_using [o5, o10, hNi])
  · intro hq p hp
    rw [me₃, f₂.val hl hp (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]) (by omega_using [o5, o10, hNi]), me₁]
    exact h.yv hq p hp
  · intro p hp
    rw [me₃]
    have g₁ : Good l t₁.mem B M l.oX p := by rw [me₁]; exact h.xg p hp
    exact g₁.of_out2 hl hp f₂ (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) (by omega_using [o5, o10, hNi])
  · intro hq p hp
    rw [me₃, f₂.val hl hp (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) (by omega_using [o5, o10, hNi]), me₁]
    exact h.xv hq p hp
  · rw [me₃]
    exact h.frame.trans (me₁ ▸ f₂.mono (by omega_using [o2, o5]) (by omega_using [hNi, o2, o5]))
  · intro r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    rw [k₃.gpr (by simp [r10]), g₂ r r1 r2 r3 r4 r6 r7 r9, k₁.gpr (by simp [r5, r6, r8]), hf.1]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  · rw [k₃.2.1, rd₂, k₁.2.1, hf.2.2.1, h.rd]
  · rw [k₃.2.2, wr₂, k₁.2.2, hf.2.2.2.1, h.wr]
  · rw [mx₃, x₂, mx₁, hf.2.2.2.2, h.mxcsr]

/-- What `convTab` starts from, `s₀`: the area's numbers, `Y ≡ R_W`,
`X ≡ x R_W`, `K1 ≡ 2^(416 R) / R_W` (`R_W = 2^(64 W)`). -/
structure ConvPre (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) : Prop where
  rbx : s₀.gpr .rbx = B
  scr : Scr s₀ B (2 * l.D)
  ar : Ar l s₀.mem B M k
  hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p)
  gx : ∀ p < 2, Good l s₀.mem B M l.oX p
  gy : ∀ p < 2, Good l s₀.mem B M l.oY p
  gk : ∀ p < 2, Good l s₀.mem B M l.oK1 p
  vx : Q → ∀ p < 2, val52 l s₀.mem B (l.D * p + l.oX) % M p = x p * 2 ^ (64 * l.W) % M p
  vy : Q → ∀ p < 2, val52 l s₀.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ (64 * l.W) % M p
  vk : Q → ∀ p < 2, val52 l s₀.mem B (l.D * p + l.oK1) % M p = 2 ^ (104 * l.S - 64 * l.W) % M p

/-- The state before entry 0, from `s₀`. -/
structure At0 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ t : State) : Prop where
  r13 : t.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 0)
  mem : t.mem = s₀.mem
  gpr : ∀ r, r ≠ .r13 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- After entry 0, `Y` in Montgomery form, from `s₀`. -/
structure At1 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k : Nat → Nat) (t : State) : Prop where
  r13 : t.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 1)
  ar : Ar l t.mem B M k
  yg : ∀ p < 2, Good l t.mem B M l.oY p
  yv : ∀ p < 2, val52 l t.mem B (l.D * p + l.oY) * 2 ^ (52 * l.S) % M p =
    val52 l s₀.mem B (l.D * p + l.oY) * val52 l s₀.mem B (l.D * p + l.oK1) % M p
  f : Out2 l B l.oY l.NB s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r13 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- Entry 0: `Y` into Montgomery form. -/
theorem conv0_ok (hl : LayOk l) {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hc : ConvPre l s₀ B M k x Q) (h : At0 l s₀ t) :
    WP isa (convTabBody l) t fun t' => At1 l s₀ B M k t' ∧ t'.zf = some false := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  unfold convTabBody
  refine bodyHead_ok hl (T_gt hl (by decide)) h.r13 (fun _ t₀ hf => ?_) fun h' => absurd h' (by decide)
  have hB₀ : t₀.gpr .rbx = B := by rw [hf.1, h.gpr _ (by decide)]; exact hc.rbx
  have h13₀ : t₀.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 0) := by rw [hf.1]; exact h.r13
  refine WP.mono (convSetup_ok hl hB₀ h13₀) fun t₁ ⟨h8, h9, h11, k₁, me₁, mx₁⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at h8 h11
  have me : t₁.mem = s₀.mem := by rw [me₁, hf.2.1, h.mem]
  have rbx₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB₀
  refine WP.seq (WP.mono (ammCore2_ok hl (o := l.oY) (M := M) (k := k) rbx₁ h8 h9 h11
    (hc.scr.congr (by rw [k₁.2.2, hf.2.2.2.1, h.wr])) (by rw [me]; exact hc.ar) (by omega_using [o2, o10])
    (by omega_using []) (by omega_using [o2, o10]) (by omega_using [o7, o10])
    (by rw [me]; exact hc.gy) (by rw [me]; exact hc.gk))
    fun t₂ ⟨hv₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 0) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁.gpr (by decide)]; exact h13₀
  refine WP.mono (bodyTail_ok hl (T_gt hl (by decide)) (by decide) r13₂) fun t₃ ⟨r13₃, z₃, k₃, me₃, mx₃⟩ =>
    ⟨⟨r13₃, by rw [me₃]; exact ar₂, fun p hp => by rw [me₃]; exact (hv₂ p hp).1,
      fun p hp => by rw [me₃, ← me]; exact (hv₂ p hp).2, by rw [me₃, ← me]; exact f₂,
      fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_, by rw [k₃.2.1, rd₂, k₁.2.1, hf.2.2.1, h.rd],
      by rw [k₃.2.2, wr₂, k₁.2.2, hf.2.2.2.1, h.wr], by rw [mx₃, x₂, mx₁, hf.2.2.2.2, h.mxcsr]⟩,
      z₃.trans (congrArg some (dec_T hl (by decide)))⟩
  rw [k₃.gpr (by simp [r10]), g₂ r r1 r2 r3 r4 r6 r7 r9, k₁.gpr (by simp [r5, r6, r8]), hf.1, h.gpr r r10]

/-- Entry 1: `X` into Montgomery form, then the table's first two entries. -/
theorem conv1_ok (hl : LayOk l) {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hc : ConvPre l s₀ B M k x Q) (h : At1 l s₀ B M k t) :
    WP isa (convTabBody l) t fun t' => TabInv l s₀ B M k x Q 2 t' ∧ t'.zf = some false := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have e2 : 2 ^ (64 * l.W) * 2 ^ (104 * l.S - 64 * l.W) = 2 ^ (52 * l.S) * 2 ^ (52 * l.S) := by
    have := dbl_le hl
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using [this]
  have hB : t.gpr .rbx = B := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hc.rbx
  -- `X` and `K1` as in `s₀`
  have gx : ∀ p < 2, Good l t.mem B M l.oX p := fun p hp =>
    (hc.gx p hp).of_out2 hl hp h.f (.inr (by omega_using [o2, o3])) (by omega_using [o3, o10]) (by omega_using [o2, o10])
  have gk : ∀ p < 2, Good l t.mem B M l.oK1 p := fun p hp =>
    (hc.gk p hp).of_out2 hl hp h.f (.inr (by omega_using [o2, o7])) (by omega_using [o7, o10]) (by omega_using [o2, o10])
  unfold convTabBody
  refine bodyHead_ok hl (T_gt hl (by decide)) h.r13 (fun _ t₀ hf => ?_) fun h' => absurd h' (by decide)
  have hB₀ : t₀.gpr .rbx = B := by rw [hf.1]; exact hB
  have h13₀ : t₀.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 1) := by rw [hf.1]; exact h.r13
  refine WP.mono (convSetup_ok hl hB₀ h13₀) fun t₁ ⟨h8, h9, h11, k₁, me₁, mx₁⟩ => ?_
  rw [show l.oY + l.NB * 1 = l.oX by omega_using [o2, o3]] at h8 h11
  have me : t₁.mem = t.mem := by rw [me₁, hf.2.1]
  have rbx₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB₀
  refine WP.seq (WP.mono (ammCore2_ok hl (o := l.oX) (M := M) (k := k) rbx₁ h8 h9 h11
    (hc.scr.congr (by rw [k₁.2.2, hf.2.2.2.1, h.wr])) (by rw [me]; exact h.ar) (by omega_using [o3, o10])
    (by omega_using [o2, o3]) (by omega_using [o3, o10]) (by omega_using [o7, o10])
    (by rw [me]; exact gx) (by rw [me]; exact gk))
    fun t₂ ⟨hv₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  rw [me] at hv₂ f₂
  have r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 1) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁.gpr (by decide)]; exact h13₀
  have hB₂ : t₂.gpr .rbx = B := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rbx₁
  have hs₂ : Scr t₂ B (2 * l.D) := hc.scr.congr (by rw [wr₂, k₁.2.2, hf.2.2.2.1, h.wr])
  -- the copies
  have hNB := NB_le hl
  refine WP.seq (WP.mono (cmp13_ok t₂ r13₂ (by omega_using [hD, o5]) (by omega_using [hD, o5]))
    fun t₃ ⟨hz, _, hg₃, hm₃, hrd₃, hwr₃, hx₃⟩ => ?_)
  rw [Nat.mul_one, decide_eq_true rfl] at hz
  have hB₃ : t₃.gpr .rbx = B := by rw [hg₃]; exact hB₂
  refine WP.seq (WP.ite true hz (fun _ => ?_) fun h' => by cases h')
  rw [WP.block_append_iff]
  refine WP.mono (copyN_ok hl hB₃ (hs₂.congr hwr₃) (by omega_using [o5, o10]) (by omega_using [o2, o10])
    (.inl (by omega_using [o2, o5]))) fun t₄ ⟨l₄, f₄, g₄, rd₄, wr₄, x₄⟩ => ?_
  have hB₄ : t₄.gpr .rbx = B := by rw [g₄]; exact hB₃
  refine WP.mono (copyN_ok hl hB₄ (hs₂.congr (by rw [wr₄, hwr₃])) (by omega_using [o5, o10]) (by omega_using [o3, o10])
    (.inl (by omega_using [o3, o5]))) fun t₅ ⟨l₅, f₅, g₅, rd₅, wr₅, x₅⟩ => ?_
  rw [hm₃] at l₄ f₄
  have r13₅ : t₅.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 1) := by rw [g₅, g₄, hg₃]; exact r13₂
  refine WP.mono (tabTail_ok hl (T_gt hl (by decide)) r13₅) fun t₆ ⟨r13₆, z₆, k₆, me₆, mx₆⟩ =>
    ⟨?_, z₆.trans (congrArg some (dec_T hl (by decide)))⟩
  have hoD : l.oTab + l.NB ≤ l.D := by omega_using [o5, o10]
  have hoD' : l.oTab + l.NB + l.NB ≤ l.D := by omega_using [o5, o10]
  -- `Y` and `X` in Montgomery form, after the conversions
  have vy₂ : Q → ∀ p < 2, val52 l t₂.mem B (l.D * p + l.oY) % M p = x p ^ 0 * 2 ^ (52 * l.S) % M p :=
    fun hq p hp => by
      rw [f₂.val hl hp (.inl (by omega_using [o2, o3])) (by omega_using [o2, o10]) (by omega_using [o3, o10])]
      exact mont_into0 (hc.hR p hp) (hc.vy hq p hp) (hc.vk hq p hp) e2 (h.yv p hp)
  have gy₂ : ∀ p < 2, Good l t₂.mem B M l.oY p := fun p hp =>
    (h.yg p hp).of_out2 hl hp f₂ (.inl (by omega_using [o2, o3])) (by omega_using [o2, o10]) (by omega_using [o3, o10])
  have vx₂ : Q → ∀ p < 2, val52 l t₂.mem B (l.D * p + l.oX) % M p = x p ^ 1 * 2 ^ (52 * l.S) % M p :=
    fun hq p hp => by
      have e := (hv₂ p hp).2
      rw [h.f.val hl hp (.inr (by omega_using [o2, o3])) (by omega_using [o3, o10]) (by omega_using [o2, o10]),
        h.f.val hl hp (.inr (by omega_using [o2, o7])) (by omega_using [o7, o10]) (by omega_using [o2, o10])] at e
      exact mont_into1 (hc.hR p hp) (hc.vx hq p hp) (hc.vk hq p hp) e2 e
  -- through the copies
  have keepY : ∀ {c : Nat}, c + l.NB ≤ l.oTab → ∀ p < 2, (Good l t₂.mem B M c p → Good l t₆.mem B M c p) ∧
      val52 l t₆.mem B (l.D * p + c) = val52 l t₂.mem B (l.D * p + c) := fun {c} hcT p hp => by
    have hcD : c + l.NB ≤ l.D := by omega_using [hcT, o5, o10]
    refine ⟨fun g => ?_, ?_⟩
    · rw [me₆]
      exact (g.of_out2 hl hp f₄ (.inl hcT) hcD hoD).of_out2 hl hp f₅ (.inl (by omega_using [hcT])) hcD hoD'
    · rw [me₆, f₅.val hl hp (.inl (by omega_using [hcT])) hcD hoD', f₄.val hl hp (.inl hcT) hcD hoD]
  refine ⟨?_, by rw [r13₆], hs₂.congr (by rw [k₆.2.2, wr₅, wr₄, hwr₃]), ?_, fun j hj p hp => ?_,
    fun p hp => (keepY (by omega_using [o2, o5]) p hp).1 (gy₂ p hp),
    fun hq p hp => by rw [(keepY (by omega_using [o2, o5]) p hp).2]; exact vy₂ hq p hp,
    fun p hp => (keepY (by omega_using [o3, o5]) p hp).1 (hv₂ p hp).1,
    fun hq p hp => by rw [(keepY (by omega_using [o3, o5]) p hp).2]; exact vx₂ hq p hp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₆.gpr (by decide), g₅, g₄, hg₃]; exact hB₂
  · rw [me₆]
    exact (ar₂.of_out2 hl f₄ (by omega_using [o2, o5]) hoD).of_out2 hl f₅ (by omega_using [o2, o5]) hoD'
  · rw [me₆]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
    · rw [Nat.mul_zero, Nat.add_zero]
      have g0 := ((gy₂ p hp).of_limbs (l₄ p hp)).of_out2 hl hp f₅ (.inl (by omega_using [])) (by omega_using [hoD']) hoD'
      refine ⟨g0, fun hq => ?_⟩
      rw [f₅.val hl hp (.inl (by omega_using [])) (by omega_using [hoD']) hoD', val52_of_limbs (l₄ p hp)]
      exact vy₂ hq p hp
    · rw [Nat.mul_one]
      have gx₄ : Good l t₄.mem B M l.oX p :=
        (hv₂ p hp).1.of_out2 hl hp f₄ (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) hoD
      refine ⟨gx₄.of_limbs (l₅ p hp), fun hq => ?_⟩
      rw [val52_of_limbs (l₅ p hp), f₄.val hl hp (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) hoD]
      exact vx₂ hq p hp
  · rw [me₆]
    have hT2 := tab_le hl (T_gt hl (show 1 < 16 by decide))
    exact (((h.f.mono (by omega_using []) (by omega_using [o2, o5, hT2])).trans
      (f₂.mono (by omega_using [o2, o3]) (by omega_using [o3, o5, hT2]))).trans
      (f₄.mono (by omega_using [o2, o5]) (by omega_using [o5, hT2]))).trans
      (f₅.mono (by omega_using [o2, o5]) (by omega_using [o5, hT2]))
  · intro r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    rw [k₆.gpr (by simp [r10]), g₅, g₄, hg₃, g₂ r r1 r2 r3 r4 r6 r7 r9, k₁.gpr (by simp [r5, r6, r8]), hf.1]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  · rw [k₆.2.1, rd₅, rd₄, hrd₃, rd₂, k₁.2.1, hf.2.2.1, h.rd]
  · rw [k₆.2.2, wr₅, wr₄, hwr₃, wr₂, k₁.2.2, hf.2.2.2.1, h.wr]
  · rw [mx₆, x₅, x₄, hx₃, x₂, mx₁, hf.2.2.2.2, h.mxcsr]

/-- The loop of `convTab`. -/
theorem convTabLoop_ok (hl : LayOk l) {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hc : ConvPre l s₀ B M k x Q) (h : At0 l s₀ t) :
    WP isa (.loop (convTabBody l) .ne) t (TabInv l s₀ B M k x Q l.T) := by
  have hT := hl.T_bounds
  refine WP.loop (M := isa) (c := .ne) (Q := TabInv l s₀ B M k x Q l.T)
    (fun n t => (n = l.T ∧ At0 l s₀ t) ∨ (n = l.T - 1 ∧ At1 l s₀ B M k t) ∨
      (1 ≤ n ∧ n ≤ l.T - 2 ∧ TabInv l s₀ B M k x Q (l.T - n) t)) ?_ l.T t (.inl ⟨rfl, h⟩)
  rintro n t (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h1, h14, hI⟩)
  · refine WP.mono (conv0_ok hl hc h) fun t' ⟨h', hz⟩ =>
      .inr ⟨?_, l.T - 1, by omega_using [hT.1, hT.2], .inr (.inl ⟨rfl, h'⟩)⟩
    simp only [eval, hz, Option.map_some, Bool.not_false]
  · refine WP.mono (conv1_ok hl hc h) fun t' ⟨h', hz⟩ =>
      .inr ⟨?_, l.T - 2, by omega_using [hT.1, hT.2], .inr (.inr ⟨by omega_using [hT.1, hT.2], Nat.le_refl _,
        by rw [show l.T - (l.T - 2) = 2 by omega_using [hT.1, hT.2]]; exact h'⟩)⟩
    simp only [eval, hz, Option.map_some, Bool.not_false]
  · refine WP.mono (tabIter_ok hl (i := l.T - n) (by omega_using [h14, h1, hT.1]) (by omega_using [h1, hT.1]) hc.hR hI)
      fun t' ⟨hI', hz⟩ => ?_
    simp only [eval, hz, Option.map_some]
    rcases Nat.eq_or_lt_of_le h1 with rfl | hn
    · rw [show l.T - 1 + 1 = l.T by omega_using [hT.1, hT.2]] at hI'
      exact .inl ⟨by simp only [show l.T - 1 + 1 = l.T by omega_using [hT.1, hT.2], decide_true, Bool.not_true], hI'⟩
    · refine .inr ⟨by simp only [decide_eq_false (show ¬ (l.T - n + 1 = l.T) by omega_using [hn, h14]),
          Bool.not_false], n - 1,
        by omega_using [hn], .inr (.inr ⟨by omega_using [hn], by omega_using [h14],
          by rw [show l.T - (n - 1) = l.T - n + 1 by omega_using [h14, hn]]; exact hI'⟩)⟩

/-- `convTab`: `Y`, `X` in Montgomery form and the table `T_i ≡ x^i 2^(208 R)`. -/
theorem convTab_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hc : ConvPre l s B M k x Q) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (convTab l)) s (TabInv l s B M k x Q l.T) := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s.setReg32 .r13 (BitVec.ofNat 32 l.oTab), rfl, WP.block_nil ?_⟩
  refine convTabLoop_ok hl hc ⟨?_, rfl, fun r hr => by rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl⟩
  rw [State.setReg32, RegUpd.gpr_setReg_self, Nat.mul_zero, Nat.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := l.oTab) (b := 2 ^ 32) (by omega_using [hD, o5]),
    Nat.mod_eq_of_lt (a := l.oTab) (b := 2 ^ 64) (by omega_using [hD, o5])]

end VG.Proof.Bignum.X86_64.Ifma
