import VerifiedGarbage.Proof.Bignum.X86_64.IfmaArea
import VerifiedGarbage.Proof.Framework.X86_64.StraightY

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

end VG.Proof.Bignum.X86_64.AmmSym
