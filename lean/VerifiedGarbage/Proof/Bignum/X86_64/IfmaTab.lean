import VerifiedGarbage.Proof.Bignum.X86_64.IfmaArea
import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSA with AVX512_IFMA on x86-64: the table

`copy160 o a` copies the numbers at `a` to `o` in both regions
(`copy160_ok`); `tabBuild` writes the table of the powers of `x`
(`tabBuild_ok`): `T_0 = Y`, `T_1 = X` and `T_i = T_(i-1) X / 2¹⁰⁴⁰`, so
`T_i ≡ x^i 2¹⁰⁴⁰` when `Y ≡ 2¹⁰⁴⁰` and `X ≡ x 2¹⁰⁴⁰`.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oTab oS oV oX oY mask52)

/-- A word of 32 bytes outside a write of 32 bytes. -/
theorem readW256_outside {m m' : Mem} {B : Addr} {d e : Nat} (h : Outside B d 32 m m')
    (he : e + 32 ≤ d ∨ d + 32 ≤ e) (he' : e + 32 ≤ 2 ^ 64) : m'.readW (off B e) 256 = m.readW (off B e) 256 :=
  (Mem.readW_congr fun i hi => (h _ (by have : i < 32 := hi; rw [ofs_off B (by omega)]; omega)).symm).symm

/-- 32-byte copies at `rbx` plus offsets, from `x.1` to `x.2`. -/
def copyCode (l : List (Nat × Nat)) : List Instr :=
  l.flatMap fun x => [.vmovdquLoad .l256 .xmm0 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx x.1),
    .vmovdquStore .l256 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx x.2) .xmm0]

theorem copies_ok {B : Addr} :
    ∀ (l : List (Nat × Nat)) (s : State), s.gpr .rbx = B → Scr s B (2 * D) →
      (∀ x ∈ l, x.1 + 32 ≤ 2 * D ∧ x.2 + 32 ≤ 2 * D) →
      (∀ x ∈ l, ∀ y ∈ l, y.1 + 32 ≤ x.2 ∨ x.2 + 32 ≤ y.1) →
      WP isa (.block (copyCode l)) s fun s' =>
        s'.mem = wrList s.mem B (l.map fun x => (x.2, s.mem.readW (off B x.1) 256)) ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | [], s, _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | (a, o) :: rest, s, hB, hs, hl, hsep => by
    have hD : D = 3872 := rfl
    have ho := hl (a, o) (List.mem_cons_self ..)
    have hn := hs.nowrap
    rw [copyCode, List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append, WP.block_cons_iff]
    have hld : InRegions (s.rd ++ s.wr) (off B a) 32 :=
      let ⟨_, h, c⟩ := hs.region (d := a) (n := 32) (by omega) (by decide); ⟨_, List.mem_append_right _ h, c⟩
    have hst : InRegions s.wr (off B o) 32 :=
      let ⟨_, h, c⟩ := hs.region (d := o) (n := 32) (by omega) (by decide); ⟨_, h, c⟩
    refine ⟨s.setV .l256 .xmm0 ((s.mem.readW (off B a) 256).extractLsb' 0 128)
      ((s.mem.readW (off B a) 256).extractLsb' 128 128),
      by simp only [exec, ea_r hB, State.load256, hld, ite_true, Option.map_some], ?_⟩
    have y₁ := StraightY.ymm_setV s .xmm0 .xmm0 ((s.mem.readW (off B a) 256).extractLsb' 0 128)
      ((s.mem.readW (off B a) 256).extractLsb' 128 128)
    simp only [ite_true, StraightY.split_eq] at y₁
    have e₁ : ∀ t : State, t = s.setV .l256 .xmm0 ((s.mem.readW (off B a) 256).extractLsb' 0 128)
        ((s.mem.readW (off B a) 256).extractLsb' 128 128) →
        t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
      rintro t rfl; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    generalize hs₁ : s.setV .l256 .xmm0 ((s.mem.readW (off B a) 256).extractLsb' 0 128)
      ((s.mem.readW (off B a) 256).extractLsb' 128 128) = s₁ at y₁ ⊢
    obtain ⟨g₁, m₁, rd₁, wr₁, x₁⟩ := e₁ s₁ hs₁.symm
    have hB₁ : s₁.gpr .rbx = B := by rw [g₁]; exact hB
    rw [WP.block_cons_iff]
    refine ⟨{ s₁ with mem := s₁.mem.writeW (off B o) (s₁.ymm .xmm0) }, by
      simp only [exec, ea_r hB₁, State.store256, wr₁, hst, ite_true], ?_⟩
    rw [y₁, m₁]
    refine WP.mono (copies_ok rest _ (by rw [← g₁] at hB; exact hB) (hs.congr wr₁)
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (fun x hx y hy => hsep x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)))
      fun s' ⟨m', g', rd', wr', x'⟩ => ⟨?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁, x'.trans x₁⟩
    rw [m', List.map_cons, wrList]
    refine congrArg (wrList _ B) (List.map_congr_left fun y hy => ?_)
    have := hl y (List.mem_cons_of_mem _ hy)
    have hs' := hsep (a, o) (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy)
    exact congrArg _ (readW256_outside (writeW256_outside _ B _ (by omega)) (by omega) (by omega))


/-- The copies of `copy160 o a`. -/
def cpList (o a : Nat) : List (Nat × Nat) :=
  (List.range 2).flatMap fun p => (List.range 5).map fun k => (D * p + a + 32 * k, D * p + o + 32 * k)

theorem copy160_eq (o a : Nat) : VG.Impl.Rsa.X86_64.CrtIfma.copy160 o a = copyCode (cpList o a) := by
  simp only [VG.Impl.Rsa.X86_64.CrtIfma.copy160, copyCode, cpList, List.flatMap_assoc, List.flatMap_map]

theorem mem_cpList {o a : Nat} {x : Nat × Nat} (h : x ∈ cpList o a) :
    ∃ p < 2, ∃ k < 5, x = (D * p + a + 32 * k, D * p + o + 32 * k) := by
  simp only [cpList, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨p, hp, k, hk, rfl⟩ := h
  exact ⟨p, hp, k, hk, rfl⟩

/-- `[o] := [a]` in both regions. -/
theorem copy160_ok {s : State} {B : Addr} {o a : Nat} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D))
    (ho : o + 160 ≤ D) (ha : a + 160 ≤ D) (hoa : a + 160 ≤ o ∨ o + 160 ≤ a) :
    WP isa (.block (VG.Impl.Rsa.X86_64.CrtIfma.copy160 o a)) s fun s' =>
      (∀ p < 2, ∀ l < 20, limb s'.mem B (D * p + o) l = limb s.mem B (D * p + a) l) ∧
      Out2 B o 160 s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : D = 3872 := rfl
  rw [copy160_eq]
  refine WP.mono (copies_ok _ s hB hs (fun x hx => ?_) (fun x hx y hy => ?_))
    fun s' ⟨hm, hg, hrd, hwr, hx⟩ => ⟨fun p hp l hl => ?_, ?_, hg, hrd, hwr, hx⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := mem_cpList hx
    rcases D_mul hp with h | h <;> dsimp only <;> omega
  · obtain ⟨p, hp, k, hk, rfl⟩ := mem_cpList hx
    obtain ⟨p', hp', k', hk', rfl⟩ := mem_cpList hy
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rcases (by omega : p' = 0 ∨ p' = 1) with rfl | rfl <;>
          dsimp only <;> omega
  · have hk : l % 5 < 5 := Nat.mod_lt _ (by decide)
    have ht : l / 5 < 4 := by omega
    have e := word_wrList_unique B (e := D * p + o + 32 * (l % 5)) (t := l / 5)
      (v := s.mem.readW (off B (D * p + a + 32 * (l % 5))) 256) ht
      (by rcases D_mul hp with h | h <;> omega)
      ((cpList o a).map fun x => (x.2, s.mem.readW (off B x.1) 256)) s.mem
      (List.mem_map.2 ⟨(D * p + a + 32 * (l % 5), D * p + o + 32 * (l % 5)),
        by simp only [cpList, List.mem_flatMap, List.mem_map, List.mem_range]; exact ⟨p, hp, l % 5, hk, rfl⟩, rfl⟩)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p', hp', k', hk', rfl⟩ := mem_cpList hy
        rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rcases (by omega : p' = 0 ∨ p' = 1) with rfl | rfl <;>
          dsimp only <;> omega)
      (fun x hx he => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p', hp', k', hk', rfl⟩ := mem_cpList hy
        dsimp only at he ⊢
        have : p' = p ∧ k' = l % 5 := by
          rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rcases (by omega : p' = 0 ∨ p' = 1) with rfl | rfl <;>
            omega
        rw [this.1, this.2])
    show (word s'.mem B _).toNat = (word s.mem B _).toNat
    have ex := readW_extract s.mem (off B (D * p + a + 32 * (l % 5))) (w := 256) (k := 8 * (l / 5)) (n := 8)
      (by omega)
    rw [hm, off_lim l, ← Nat.add_assoc, e, ← Nat.add_assoc, show 64 * (l / 5) = 8 * (8 * (l / 5)) by omega]
    refine congrArg BitVec.toNat (ex.trans ?_)
    rw [off_add]
  · rw [hm]
    exact wrList_out2 B (by omega) _ s.mem fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨p, hp, k, hk, rfl⟩ := mem_cpList hy
      exact ⟨p, hp, by dsimp only; omega, by dsimp only; omega⟩


/-- `tabBuild`'s operands for entry `i`: `r8` at `T_(i-1)`, `r9` at `X`, `r11` at `T_i`. -/
theorem tabHead_ok {s : State} {B : Addr} {i : Nat} (hi : 1 ≤ i) (hi' : i < 16) (hB : s.gpr .rbx = B)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (oTab + 160 * i)) :
    WP isa (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm 160),
        .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 oX)), .mov .r11 (.reg .rbx),
        .alu .add .r11 (.reg .r13)]) s fun s' =>
      s'.gpr .r8 = off B (oTab + 160 * (i - 1)) ∧ s'.gpr .r9 = off B oX ∧ s'.gpr .r11 = off B (oTab + 160 * i) ∧
      VG.Proof.MlKem.X86_64.Keep [.r8, .r9, .r11] s s' ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .r9, .r11] (Q := fun s' =>
    s'.gpr .r8 = off B (oTab + 160 * (i - 1)) ∧ s'.gpr .r9 = off B oX ∧ s'.gpr .r11 = off B (oTab + 160 * i) ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr) (by
    xrun [hB, h13, sx160, se_ofNat (show oX < 2 ^ 31 by decide)]
    and_intros
    any_goals rfl
    · rw [VG.Offset.add_ofNat_sub _ (by simp only [oTab]; omega)]
      exact congrArg (off B) (by simp only [oTab]; omega)) rfl)
    fun s' ⟨⟨a, b, c, d, e, f, g⟩, k⟩ => ⟨a, b, c, k, d, e, f, g⟩

/-- `tabBuild`'s next entry, `ZF` after the last. -/
theorem tabTail_ok {s : State} {i : Nat} (hi : i < 16) (h13 : s.gpr .r13 = BitVec.ofNat 64 (oTab + 160 * i)) :
    WP isa (.block [.alu .add .r13 (.imm 160), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (oTab + 2560)))]) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (oTab + 160 * (i + 1)) ∧ s'.zf = some (decide (i + 1 = 16)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun s' =>
    s'.gpr .r13 = BitVec.ofNat 64 (oTab + 160 * (i + 1)) ∧ s'.zf = some (decide (i + 1 = 16)) ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr) (by
    xrun [h13, sx160, se_ofNat (show oTab + 2560 < 2 ^ 31 by decide)]
    and_intros
    · rw [← BitVec.ofNat_add]; congr 1
    · rw [← BitVec.ofNat_add, ofNat_sub_beq (by simp only [oTab]; omega) (by decide)]
      exact decide_eq_decide.mpr (by simp only [oTab]; omega)
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d, e, f⟩, k⟩ => ⟨a, b, k, c, d, e, f⟩


/-- After the entries below `i` of the table, from `s₀`. -/
structure TabInv (s₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (i : Nat) (t : State) : Prop where
  rbx : t.gpr .rbx = B
  r13 : t.gpr .r13 = BitVec.ofNat 64 (oTab + 160 * i)
  scr : Scr t B (2 * D)
  ar : Ar t.mem B M k
  tab : ∀ j < i, ∀ p < 2, Good t.mem B M (oTab + 160 * j) p ∧
    (Q → val52 t.mem B (D * p + (oTab + 160 * j)) % M p = x p ^ j * 2 ^ (52 * 20) % M p)
  xg : ∀ p < 2, Good t.mem B M oX p
  xv : Q → ∀ p < 2, val52 t.mem B (D * p + oX) % M p = x p ^ 1 * 2 ^ (52 * 20) % M p
  frame : Out2 B oTab 2560 s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r13 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- Entry `i` of the table. -/
theorem tabIter_ok {s₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {i : Nat} (hi : 2 ≤ i) (hi' : i < 16)
    (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p)) (h : TabInv s₀ B M k x Q i t) :
    WP isa (.seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm 160),
        .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 oX)), .mov .r11 (.reg .rbx),
        .alu .add .r11 (.reg .r13)])
      (.seq VG.Impl.Rsa.X86_64.CrtIfma.ammCore
        (.block [.alu .add .r13 (.imm 160), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (oTab + 2560)))]))) t
      fun t' => TabInv s₀ B M k x Q (i + 1) t' ∧ t'.zf = some (decide (i + 1 = 16)) := by
  have hD : D = 3872 := rfl
  refine WP.seq (WP.mono (tabHead_ok (by omega) hi' h.rbx h.r13) fun t₁ ⟨h8, h9, h11, k₁, me₁, x₁, y₁, mx₁⟩ => ?_)
  have rbx₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact h.rbx
  have hg : ∀ p < 2, Good t₁.mem B M (oTab + 160 * (i - 1)) p := fun p hp => by
    rw [me₁]; exact (h.tab (i - 1) (by omega) p hp).1
  refine WP.seq (WP.mono (ammCore2_ok (o := oTab + 160 * i) (k := k) rbx₁ h8 h9 h11 (h.scr.congr k₁.2.2)
    (by rw [me₁]; exact h.ar) (by simp only [oTab]; omega) (by simp only [oTab]; omega)
    (by simp only [oTab]; omega) (by simp only [oX]; omega) hg (fun p hp => by rw [me₁]; exact h.xg p hp))
    fun t₂ ⟨hv₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (oTab + 160 * i) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁.gpr (by decide)]; exact h.r13
  refine WP.mono (tabTail_ok hi' r13₂) fun t₃ ⟨r13₃, z₃, k₃, me₃, x₃, y₃, mx₃⟩ => ⟨⟨?_, r13₃, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩, z₃⟩
  · rw [k₃.gpr (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact rbx₁
  · exact h.scr.congr (by rw [k₃.2.2, wr₂, k₁.2.2])
  · rw [me₃]; exact ar₂
  · have hoD : oTab + 160 * i + 160 ≤ D := by simp only [oTab]; omega
    intro j hj p hp
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
    · have hc : oTab + 160 * j + 160 ≤ oTab + 160 * i ∨ oTab + 160 * i + 160 ≤ oTab + 160 * j := .inl (by omega)
      have hcD : oTab + 160 * j + 160 ≤ D := by simp only [oTab]; omega
      obtain ⟨g, v⟩ := h.tab j hj p hp
      refine ⟨?_, fun hq => ?_⟩
      · have g₁ : Good t₁.mem B M (oTab + 160 * j) p := by rw [me₁]; exact g
        rw [me₃]; exact g₁.of_out2 hp f₂ hc hcD hoD
      · rw [me₃, f₂.val hp hc hcD hoD, me₁]; exact v hq
    · obtain ⟨g, v⟩ := hv₂ p hp
      refine ⟨by rw [me₃]; exact g, fun hq => ?_⟩
      rw [me₁] at v
      have e := mont_mul2 (R := 2 ^ (52 * 20)) (hR p hp) ((h.tab (j - 1) (by omega) p hp).2 hq) (h.xv hq p hp) v
      rw [show j - 1 + 1 = j by omega] at e
      rw [me₃]; exact e
  · intro p hp
    rw [me₃]
    have g₁ : Good t₁.mem B M oX p := by rw [me₁]; exact h.xg p hp
    exact g₁.of_out2 hp f₂
      (.inl (by simp only [oX, oTab]; omega)) (by simp only [oX, D]; omega) (by simp only [oTab]; omega)
  · intro hq p hp
    rw [me₃, f₂.val hp (.inl (by simp only [oX, oTab]; omega)) (by simp only [oX, D]; omega)
      (by simp only [oTab]; omega), me₁]
    exact h.xv hq p hp
  · rw [me₃]
    exact h.frame.trans (me₁ ▸ f₂.mono (by omega) (by omega))
  · intro r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    rw [k₃.gpr (by simp [r10]), g₂ r r1 r2 r3 r4 r6 r7 r9, k₁.gpr (by simp [r5, r6, r8])]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  · rw [k₃.2.1, rd₂, k₁.2.1, h.rd]
  · rw [k₃.2.2, wr₂, k₁.2.2, h.wr]
  · rw [mx₃, x₂, mx₁, h.mxcsr]


/-- The loop of `tabBuild`, from entry `16 - n`. -/
theorem tabLoop_ok {s₀ : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p)) :
    ∀ n t, 1 ≤ n → n ≤ 14 → TabInv s₀ B M k x Q (16 - n) t →
      WP isa (.loop (.seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm 160),
        .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 oX)), .mov .r11 (.reg .rbx),
        .alu .add .r11 (.reg .r13)])
      (.seq VG.Impl.Rsa.X86_64.CrtIfma.ammCore
        (.block [.alu .add .r13 (.imm 160), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (oTab + 2560)))]))) .ne) t
        (TabInv s₀ B M k x Q 16) := by
  intro n t h1 h14 hI
  refine WP.loop (M := isa) (c := .ne) (Q := TabInv s₀ B M k x Q 16)
    (fun n t => 1 ≤ n ∧ n ≤ 14 ∧ TabInv s₀ B M k x Q (16 - n) t) ?_ n t ⟨h1, h14, hI⟩
  intro n t ⟨h1, h14, hI⟩
  refine WP.mono (tabIter_ok (i := 16 - n) (by omega) (by omega) hR hI) fun t' ⟨hI', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · exact .inl ⟨by simp, hI'⟩
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (16 - n + 1 = 16) by omega), Bool.not_false], n - 1,
      by omega, by omega, by omega, by rw [show 16 - (n - 1) = 16 - n + 1 by omega]; exact hI'⟩

/-- The table: `T_i ≡ x^i 2¹⁰⁴⁰` from `Y ≡ 2¹⁰⁴⁰` and `X ≡ x 2¹⁰⁴⁰`. -/
theorem tabBuild_ok {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * D)) (ar : Ar s.mem B M k) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p))
    (gy : ∀ p < 2, Good s.mem B M oY p) (gx : ∀ p < 2, Good s.mem B M oX p)
    (vy : Q → ∀ p < 2, val52 s.mem B (D * p + oY) % M p = x p ^ 0 * 2 ^ (52 * 20) % M p)
    (vx : Q → ∀ p < 2, val52 s.mem B (D * p + oX) % M p = x p ^ 1 * 2 ^ (52 * 20) % M p) :
    WP isa (VG.Impl.Bignum.X86_64.seqs VG.Impl.Rsa.X86_64.CrtIfma.tabBuild) s (TabInv s B M k x Q 16) := by
  have hD : D = 3872 := rfl
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy160_ok hB hs (by decide) (by decide)
    (.inl (by decide))) fun s₁ ⟨l₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_
  rw [WP.block_append_iff]
  have hB₁ : s₁.gpr .rbx = B := by rw [g₁]; exact hB
  refine WP.mono (copy160_ok hB₁ (hs.congr wr₁) (by decide) (by decide)
    (.inl (by decide))) fun s₂ ⟨l₂, f₂, g₂, rd₂, wr₂, x₂⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨s₂.setReg32 .r13 (BitVec.ofNat 32 (oTab + 320)), rfl, WP.block_nil ?_⟩
  have g₃ : ∀ r, r ≠ .r13 → (s₂.setReg32 .r13 (BitVec.ofNat 32 (oTab + 320))).gpr r = s.gpr r := fun r hr => by
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr, g₂, g₁]
  have hoD : oTab + 160 ≤ D := by decide
  have hoD' : oTab + 160 + 160 ≤ D := by decide
  -- the numbers after the copies
  have gx₁ : ∀ p < 2, Good s₁.mem B M oX p := fun p hp => (gx p hp).of_out2 hp f₁ (.inl (by decide)) (by decide) hoD
  have vx₁ : ∀ p < 2, val52 s₁.mem B (D * p + oX) = val52 s.mem B (D * p + oX) := fun p hp =>
    f₁.val hp (.inl (by decide)) (by decide) hoD
  have gx₂ : ∀ p < 2, Good s₂.mem B M oX p := fun p hp =>
    (gx₁ p hp).of_out2 hp f₂ (.inl (by decide)) (by decide) hoD'
  have vx₂ : ∀ p < 2, val52 s₂.mem B (D * p + oX) = val52 s.mem B (D * p + oX) := fun p hp => by
    rw [f₂.val hp (.inl (by decide)) (by decide) hoD', vx₁ p hp]
  have g0 : ∀ p < 2, Good s₂.mem B M oTab p := fun p hp =>
    ((gy p hp).of_limbs (l₁ p hp)).of_out2 hp f₂ (.inl (by decide)) (by decide) hoD'
  have v0 : ∀ p < 2, val52 s₂.mem B (D * p + oTab) = val52 s.mem B (D * p + oY) := fun p hp => by
    rw [f₂.val hp (.inl (by decide)) (by decide) hoD', val52_of_limbs (l₁ p hp)]
  have g1 : ∀ p < 2, Good s₂.mem B M (oTab + 160) p := fun p hp => (gx₁ p hp).of_limbs (l₂ p hp)
  have v1 : ∀ p < 2, val52 s₂.mem B (D * p + (oTab + 160)) = val52 s.mem B (D * p + oX) := fun p hp => by
    rw [val52_of_limbs (l₂ p hp), vx₁ p hp]
  generalize ht₃ : s₂.setReg32 .r13 (BitVec.ofNat 32 (oTab + 320)) = t₃ at g₃
  have e₃ : t₃.mem = s₂.mem ∧ t₃.rd = s₂.rd ∧ t₃.wr = s₂.wr ∧ t₃.mxcsr = s₂.mxcsr := by
    rw [← ht₃]; exact ⟨rfl, rfl, rfl, rfl⟩
  have r13₃ : t₃.gpr .r13 = BitVec.ofNat 64 (oTab + 160 * 2) := by
    rw [← ht₃, State.setReg32, RegUpd.gpr_setReg_self]; decide
  refine tabLoop_ok hR 14 _ (by decide) (Nat.le_refl _) ⟨?_, r13₃, hs.congr (by rw [e₃.2.2.1, wr₂, wr₁]),
    ?_, fun j hj p hp => ?_, ?_, ?_, ?_, fun r _ _ _ _ _ _ _ _ _ r13 => g₃ r r13, by rw [e₃.2.1, rd₂, rd₁],
    by rw [e₃.2.2.1, wr₂, wr₁], by rw [e₃.2.2.2, x₂, x₁]⟩
  · exact (g₃ .rbx (by decide)).trans hB
  · rw [e₃.1]; exact (ar.of_out2 f₁ (by decide) hoD).of_out2 f₂ (by decide) hoD'
  · rw [e₃.1]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [Nat.mul_zero, Nat.add_zero]
      exact ⟨g0 p hp, fun hq => by rw [v0 p hp]; exact vy hq p hp⟩
    · rw [Nat.mul_one]
      exact ⟨g1 p hp, fun hq => by rw [v1 p hp]; exact vx hq p hp⟩
  · rw [e₃.1]; exact gx₂
  · intro hq p hp; rw [e₃.1, vx₂ p hp]; exact vx hq p hp
  · rw [e₃.1]; exact (f₁.mono (by decide) (by decide)).trans (f₂.mono (by decide) (by decide))
end VG.Proof.Bignum.X86_64.AmmSym
