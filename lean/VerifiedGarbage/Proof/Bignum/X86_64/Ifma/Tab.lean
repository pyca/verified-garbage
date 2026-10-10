import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Area
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: the table

`copyN o a` copies the numbers at `a` to `o` in
both regions (`copyN_ok`); `tabBuild` writes the table of the powers of `x`
(`tabBuild_ok`): `T_0 = Y`, `T_1 = X` and `T_i = T_(i-1) X / 2^(208 R)`, so
`T_i ≡ x^i 2^(208 R)` when `Y ≡ 2^(208 R)` and `X ≡ x 2^(208 R)`.
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (wrList writeW256_outside word_wrList_unique readW256_outside off_add se_ofNat
  mont_mul2)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The offsets of a region, in `NB` and `E`. -/
theorem lay_offs (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : l.oK0 = l.NB ∧ l.oY = l.NB + 32 ∧ l.oX = 2 * l.NB + 32 ∧ l.oS = 3 * l.NB + 32 ∧
    l.oTab = 4 * l.NB + 32 ∧ l.oE = 20 * l.NB + 32 ∧ l.oK1 = 20 * l.NB + 32 + l.E ∧
    l.oV = 21 * l.NB + 32 + l.E ∧ l.oFin = 21 * l.NB + 64 + l.E ∧ l.D = 22 * l.NB + 64 + l.E := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Lay.D, Lay.oFin, Lay.oV, Lay.oK1, Lay.oE, Lay.oTab, Lay.oS, Lay.oX, Lay.oY, Lay.oK0] <;> omega_using []

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

/-- `tabBuild`'s operands for entry `i`: `r8` at `T_(i-1)`, `r9` at `X`, `r11` at `T_i`. -/
theorem tabHead_ok (hl : LayOk l) {s : State} {B : Addr} {i : Nat} (hi : 1 ≤ i) (_hi' : i < 16)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm (BitVec.ofNat 32 l.NB)),
        .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 l.oX)), .mov .r11 (.reg .rbx),
        .alu .add .r11 (.reg .r13)]) s fun s' =>
      s'.gpr .r8 = off B (l.oTab + l.NB * (i - 1)) ∧ s'.gpr .r9 = off B l.oX ∧
      s'.gpr .r11 = off B (l.oTab + l.NB * i) ∧
      VG.Proof.MlKem.X86_64.Keep [.r8, .r9, .r11] s s' ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNi : l.NB ≤ l.NB * i := Nat.le_mul_of_pos_right _ (by omega_using [hi])
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .r9, .r11] (Q := fun s' =>
    s'.gpr .r8 = off B (l.oTab + l.NB * (i - 1)) ∧ s'.gpr .r9 = off B l.oX ∧
      s'.gpr .r11 = off B (l.oTab + l.NB * i) ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr) (by
    xrun [hB, h13, se_ofNat (show l.NB < 2 ^ 31 by omega_using [hD]), se_ofNat (show l.oX < 2 ^ 31 by omega_using [hD, o3])]
    and_intros
    any_goals rfl
    · rw [VG.Offset.add_ofNat_sub _ (by omega_using [hNi])]
      exact congrArg (off B) (by rw [Nat.mul_sub_one]; omega_using [hNi])) rfl)
    fun s' ⟨⟨a, b, c, d, e, f, g⟩, k⟩ => ⟨a, b, c, k, d, e, f, g⟩

/-- `tabBuild`'s next entry, `ZF` after the last. -/
theorem tabTail_ok (hl : LayOk l) {s : State} {i : Nat} (hi : i < 16)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)) :
    WP isa (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
        .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + 16 * l.NB)))]) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * (i + 1)) ∧ s'.zf = some (decide (i + 1 = 16)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNi : l.NB * i ≤ l.NB * 15 := Nat.mul_le_mul_left _ (by omega_using [hi])
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun s' =>
    s'.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * (i + 1)) ∧ s'.zf = some (decide (i + 1 = 16)) ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr) (by
    xrun [h13, se_ofNat (show l.NB < 2 ^ 31 by omega_using [hD]), se_ofNat (show l.oTab + 16 * l.NB < 2 ^ 31 by omega_using [hD, o5])]
    and_intros
    · rw [← BitVec.ofNat_add]; congr 1; rw [Nat.mul_succ]; omega_using []
    · rw [← BitVec.ofNat_add, ofNat_sub_beq (by omega_using [hD, o5, hNi]) (by omega_using [hD, o5])]
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
      · rcases Nat.lt_or_ge (i + 1) 16 with h' | h'
        · have := Nat.mul_le_mul_left l.NB (show i + 1 ≤ 15 by omega_using [h'])
          rw [Nat.mul_succ] at this
          have := NB_le hl
          omega_arith
        · omega_using [hi, h']
      · obtain rfl : i = 15 := by omega_using [h]
        omega_using []
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d, e, f⟩, k⟩ => ⟨a, b, k, c, d, e, f⟩

/-- After the entries below `i` of the table, from `s₀`. -/
structure TabInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (i : Nat) (t : State) : Prop where
  rbx : t.gpr .rbx = B
  r13 : t.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i)
  scr : Scr t B (2 * l.D)
  ar : Ar l t.mem B M k
  tab : ∀ j < i, ∀ p < 2, Good l t.mem B M (l.oTab + l.NB * j) p ∧
    (Q → val52 l t.mem B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.L) % M p)
  xg : ∀ p < 2, Good l t.mem B M l.oX p
  xv : Q → ∀ p < 2, val52 l t.mem B (l.D * p + l.oX) % M p = x p ^ 1 * 2 ^ (52 * l.L) % M p
  frame : Out2 l B l.oTab (16 * l.NB) s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r13 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- The body of `tabBuild`'s loop. -/
def tabBody (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm (BitVec.ofNat 32 l.NB)),
      .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 l.oX)), .mov .r11 (.reg .rbx),
      .alu .add .r11 (.reg .r13)])
    (.seq (ammCore l) (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
      .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + 16 * l.NB)))]))

/-- Entry `i` of the table. -/
theorem tabIter_ok (hl : LayOk l) {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {i : Nat}
    (hi : 2 ≤ i) (hi' : i < 16) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p))
    (h : TabInv l s₀ B M k x Q i t) :
    WP isa (tabBody l) t fun t' => TabInv l s₀ B M k x Q (i + 1) t' ∧ t'.zf = some (decide (i + 1 = 16)) := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNi : l.NB * i ≤ l.NB * 15 := Nat.mul_le_mul_left _ (by omega_using [hi'])
  have hNi1 : l.NB * (i - 1) + l.NB = l.NB * i := by
    rw [← Nat.mul_succ, show (i - 1).succ = i by omega_using [hi]]
  refine WP.seq (WP.mono (tabHead_ok hl (by omega_using [hi]) hi' h.rbx h.r13) fun t₁ ⟨h8, h9, h11, k₁, me₁, x₁, y₁, mx₁⟩ => ?_)
  have rbx₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact h.rbx
  have hg : ∀ p < 2, Good l t₁.mem B M (l.oTab + l.NB * (i - 1)) p := fun p hp => by
    rw [me₁]; exact (h.tab (i - 1) (by omega_using [hi]) p hp).1
  refine WP.seq (WP.mono (ammCore2_ok hl (o := l.oTab + l.NB * i) (k := k) rbx₁ h8 h9 h11 (h.scr.congr k₁.2.2)
    (by rw [me₁]; exact h.ar) (by omega_using [o5, o10, hNi]) (by omega_using [o2, o5])
        (by omega_using [o5, o10, hNi, hNi1]) (by omega_using [o3, o10]) hg
    (fun p hp => by rw [me₁]; exact h.xg p hp))
    fun t₂ ⟨hv₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * i) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁.gpr (by decide)]; exact h.r13
  refine WP.mono (tabTail_ok hl hi' r13₂) fun t₃ ⟨r13₃, z₃, k₃, me₃, x₃, y₃, mx₃⟩ => ⟨⟨?_, r13₃, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩, z₃⟩
  · rw [k₃.gpr (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact rbx₁
  · exact h.scr.congr (by rw [k₃.2.2, wr₂, k₁.2.2])
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
      have e := mont_mul2 (R := 2 ^ (52 * l.L)) (hR p hp) ((h.tab (j - 1) (by omega_using [hi]) p hp).2 hq) (h.xv hq p hp) v
      rw [show j - 1 + 1 = j by omega_using [hi]] at e
      rw [me₃]; exact e
  · intro p hp
    rw [me₃]
    have g₁ : Good l t₁.mem B M l.oX p := by rw [me₁]; exact h.xg p hp
    exact g₁.of_out2 hl hp f₂ (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) (by omega_using [o5, o10, hNi])
  · intro hq p hp
    rw [me₃, f₂.val hl hp (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) (by omega_using [o5, o10, hNi]), me₁]
    exact h.xv hq p hp
  · rw [me₃]
    exact h.frame.trans (me₁ ▸ f₂.mono (by omega_using []) (by omega_using [hNi]))
  · intro r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    rw [k₃.gpr (by simp [r10]), g₂ r r1 r2 r3 r4 r6 r7 r9, k₁.gpr (by simp [r5, r6, r8])]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  · rw [k₃.2.1, rd₂, k₁.2.1, h.rd]
  · rw [k₃.2.2, wr₂, k₁.2.2, h.wr]
  · rw [mx₃, x₂, mx₁, h.mxcsr]

/-- The loop of `tabBuild`, from entry `16 - n`. -/
theorem tabLoop_ok (hl : LayOk l) {s₀ : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p)) :
    ∀ n t, 1 ≤ n → n ≤ 14 → TabInv l s₀ B M k x Q (16 - n) t →
      WP isa (.loop (tabBody l) .ne) t (TabInv l s₀ B M k x Q 16) := by
  intro n t h1 h14 hI
  refine WP.loop (M := isa) (c := .ne) (Q := TabInv l s₀ B M k x Q 16)
    (fun n t => 1 ≤ n ∧ n ≤ 14 ∧ TabInv l s₀ B M k x Q (16 - n) t) ?_ n t ⟨h1, h14, hI⟩
  intro n t ⟨h1, h14, hI⟩
  refine WP.mono (tabIter_ok hl (i := 16 - n) (by omega_using [h14]) (by omega_using [h1]) hR hI) fun t' ⟨hI', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · exact .inl ⟨by simp, hI'⟩
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (16 - n + 1 = 16) by omega_using [hn]), Bool.not_false], n - 1,
      by omega_using [hn], by omega_using [hn], by omega_using [h14], by rw [show 16 - (n - 1) = 16 - n + 1 by omega_using [h14, hn]]; exact hI'⟩

/-- The table: `T_i ≡ x^i 2^(208 R)` from `Y ≡ 2^(208 R)` and `X ≡ x 2^(208 R)`. -/
theorem tabBuild_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * l.D)) (ar : Ar l s.mem B M k) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p))
    (gy : ∀ p < 2, Good l s.mem B M l.oY p) (gx : ∀ p < 2, Good l s.mem B M l.oX p)
    (vy : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oY) % M p = x p ^ 0 * 2 ^ (52 * l.L) % M p)
    (vx : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oX) % M p = x p ^ 1 * 2 ^ (52 * l.L) % M p) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (tabBuild l)) s (TabInv l s B M k x Q 16) := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyN_ok hl hB hs (by omega_using [o5, o10]) (by omega_using [o2, o10])
    (.inl (by omega_using [o2, o5]))) fun s₁ ⟨l₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_
  rw [WP.block_append_iff]
  have hB₁ : s₁.gpr .rbx = B := by rw [g₁]; exact hB
  refine WP.mono (copyN_ok hl hB₁ (hs.congr wr₁) (by omega_using [o5, o10]) (by omega_using [o3, o10])
    (.inl (by omega_using [o3, o5]))) fun s₂ ⟨l₂, f₂, g₂, rd₂, wr₂, x₂⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨s₂.setReg32 .r13 (BitVec.ofNat 32 (l.oTab + 2 * l.NB)), rfl, WP.block_nil ?_⟩
  have g₃ : ∀ r, r ≠ .r13 → (s₂.setReg32 .r13 (BitVec.ofNat 32 (l.oTab + 2 * l.NB))).gpr r = s.gpr r :=
    fun r hr => by rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr, g₂, g₁]
  have hoD : l.oTab + l.NB ≤ l.D := by omega_using [o5, o10]
  have hoD' : l.oTab + l.NB + l.NB ≤ l.D := by omega_using [o5, o10]
  -- the numbers after the copies
  have gx₁ : ∀ p < 2, Good l s₁.mem B M l.oX p := fun p hp =>
    (gx p hp).of_out2 hl hp f₁ (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) hoD
  have vx₁ : ∀ p < 2, val52 l s₁.mem B (l.D * p + l.oX) = val52 l s.mem B (l.D * p + l.oX) := fun p hp =>
    f₁.val hl hp (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) hoD
  have gx₂ : ∀ p < 2, Good l s₂.mem B M l.oX p := fun p hp =>
    (gx₁ p hp).of_out2 hl hp f₂ (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) hoD'
  have vx₂ : ∀ p < 2, val52 l s₂.mem B (l.D * p + l.oX) = val52 l s.mem B (l.D * p + l.oX) := fun p hp => by
    rw [f₂.val hl hp (.inl (by omega_using [o3, o5])) (by omega_using [o3, o10]) hoD', vx₁ p hp]
  have g0 : ∀ p < 2, Good l s₂.mem B M l.oTab p := fun p hp =>
    ((gy p hp).of_limbs (l₁ p hp)).of_out2 hl hp f₂ (.inl (by omega_using [])) (by omega_using [hoD']) hoD'
  have v0 : ∀ p < 2, val52 l s₂.mem B (l.D * p + l.oTab) = val52 l s.mem B (l.D * p + l.oY) := fun p hp => by
    rw [f₂.val hl hp (.inl (by omega_using [])) (by omega_using [hoD']) hoD', val52_of_limbs (l₁ p hp)]
  have g1 : ∀ p < 2, Good l s₂.mem B M (l.oTab + l.NB) p := fun p hp => (gx₁ p hp).of_limbs (l₂ p hp)
  have v1 : ∀ p < 2, val52 l s₂.mem B (l.D * p + (l.oTab + l.NB)) = val52 l s.mem B (l.D * p + l.oX) :=
    fun p hp => by rw [val52_of_limbs (l₂ p hp), vx₁ p hp]
  generalize ht₃ : s₂.setReg32 .r13 (BitVec.ofNat 32 (l.oTab + 2 * l.NB)) = t₃ at g₃
  have e₃ : t₃.mem = s₂.mem ∧ t₃.rd = s₂.rd ∧ t₃.wr = s₂.wr ∧ t₃.mxcsr = s₂.mxcsr := by
    rw [← ht₃]; exact ⟨rfl, rfl, rfl, rfl⟩
  have r13₃ : t₃.gpr .r13 = BitVec.ofNat 64 (l.oTab + l.NB * 2) := by
    rw [← ht₃, State.setReg32, RegUpd.gpr_setReg_self, Nat.mul_comm l.NB 2]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [hD, hoD']), Nat.mod_eq_of_lt (by omega_using [hD, hoD'])]
  refine tabLoop_ok hl hR 14 _ (by decide) (Nat.le_refl _) ⟨?_, r13₃, hs.congr (by rw [e₃.2.2.1, wr₂, wr₁]),
    ?_, fun j hj p hp => ?_, ?_, ?_, ?_, fun r _ _ _ _ _ _ _ _ _ r13 => g₃ r r13, by rw [e₃.2.1, rd₂, rd₁],
    by rw [e₃.2.2.1, wr₂, wr₁], by rw [e₃.2.2.2, x₂, x₁]⟩
  · exact (g₃ .rbx (by decide)).trans hB
  · rw [e₃.1]; exact (ar.of_out2 hl f₁ (by omega_using [o2, o5]) hoD).of_out2 hl f₂ (by omega_using [o2, o5]) hoD'
  · rw [e₃.1]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
    · rw [Nat.mul_zero, Nat.add_zero]
      exact ⟨g0 p hp, fun hq => by rw [v0 p hp]; exact vy hq p hp⟩
    · rw [Nat.mul_one]
      exact ⟨g1 p hp, fun hq => by rw [v1 p hp]; exact vx hq p hp⟩
  · rw [e₃.1]; exact gx₂
  · intro hq p hp; rw [e₃.1, vx₂ p hp]; exact vx hq p hp
  · rw [e₃.1]; exact (f₁.mono (by omega_using []) (by omega_using [])).trans (f₂.mono (by omega_using []) (by omega_using []))

end VG.Proof.Bignum.X86_64.Ifma
