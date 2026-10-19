module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
public import VerifiedGarbage.Impl.Weierstrass.AArch64
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Montgomery products modulo a general modulus, as functions, on AArch64

`mulFnG n m` (`Impl/Weierstrass/AArch64/Mont.lean`), for a modulus whose
reduction multiplies by its words (such as a curve's order), zero-extends the
offsets (`zext_ok`), saves the callee-saved registers it writes in vector
lanes (`saves_ok`), computes the pointers `ro`, `ra` and `rb` (`ptrsG_ok`),
writes the modulus into its own working space at `moAt n` (`setConst_ok`),
runs the inline product through the pointers (`mulR_okW`) and restores the
registers (`mulFnG_ok`): what `mulFnS_ok` gives for the other moduli. `ModOk`
is either's hypotheses, and `mulFn_ok` the function's product for both.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- What the general form needs of the modulus `m` of `n` words: six or nine
words, `m` below `2^(64 n)`, `minv m` its inverse's negation, what the
inline product needs of it, the general form's reduction, and code that
writes no vector register. -/
structure ModOkG (n m : Nat) : Prop where
  hn : n = 6 ∨ n = 8 ∨ n = 9
  m_lt : m < 2 ^ (64 * n)
  inv : (m * minv m + 1) % 2 ^ 64 = 0
  red : (mod n m).ok m = true
  g : general n m = true
  novec : ∀ i ∈ ptrsG ++ (setMod n m ++ mulR (mod n m) raG rbG roG 0 0 0), vdstOf i = none

/-- What the function needs of the modulus: either form's hypotheses. -/
def ModOk (n m : Nat) : Prop := ModOkS n m ∨ ModOkG n m

theorem ModOk.n9 {n m : Nat} (h : ModOk n m) : n ≤ 9 := by
  rcases h with h | h
  · exact h.n9
  · rcases h.hn with h | h | h <;> omega

theorem ModOk.n4 {n m : Nat} (h : ModOk n m) : 4 ≤ n := by
  rcases h with h | h
  · exact h.n4
  · rcases h.hn with h | h | h <;> omega

theorem ModOk.hn' {n m : Nat} (h : ModOk n m) : n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 9 := by
  rcases h with h | h
  · rcases h.hn' with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr h))
  · exact .inr h.hn

theorem ModOk.inv {n m : Nat} (h : ModOk n m) : (m * minv m + 1) % 2 ^ 64 = 0 := by
  rcases h with h | h
  · exact h.inv
  · exact h.inv

/-- What the general form needs of its registers. -/
structure RegsG (n : Nat) : Prop where
  n10 : n < 10
  pa : PtrOk n raG
  pb : PtrOk n rbG
  po : roG ∉ clob n
  slen : (savedG n).length ≤ 10
  snd : (savedG n).Nodup
  spres : ∀ r ∈ savedG n, r ∈ preserved
  pres : ∀ r ∈ preserved, r ∉ savedG n → r ∉ clob n ∧ r ∉ [raG, rbG, roG, .x1, .x2, .x3]
  keep0 : ∀ r ∈ [Reg.x0, .x19, .x20], r ∉ clob n ∧ r ∉ savedG n ∧ r ∉ [raG, rbG, roG, .x1, .x2, .x3]

theorem regsG_ok : ∀ n, (n = 6 ∨ n = 8 ∨ n = 9) → RegsG n := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;> exact ⟨by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem ptrsG_ok (s : State) :
    WP isa (.block ptrsG) s fun s' =>
      s'.gpr roG = s.gpr .x0 + s.gpr .x1 ∧ s'.gpr raG = s.gpr .x0 + s.gpr .x2 ∧
      s'.gpr rbG = s.gpr .x0 + s.gpr .x3 ∧ Keeps [raG, rbG, roG] s s' ∧ s'.v = s.v := by
  apply WP.of_runBlock
  simp only [ptrsG, raG, rbG, roG, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left', State.read, BitVec.setWidth_eq]
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  all_goals simp only [RegUpd.gpr_write]
  all_goals simp_all

theorem mulFnG_wp (n m : Nat) {s : State} {Q : State → Prop} : WP isa (mulFnG n m) s Q ↔
    WP isa (.block (zextCode ++ (saveCodeG n ++ (ptrsG ++ (setMod n m ++
      (mulR (mod n m) raG rbG roG 0 0 0 ++ restoreCodeG n)))))) s Q := by
  rw [mulFnG, WP.seq_iff, ← WP.block_append_iff]
  simp only [List.append_assoc]

theorem saveCodeG_eq (n : Nat) : saveCodeG n = insCode (savedG n) 0 := rfl
theorem restoreCodeG_eq (n : Nat) : restoreCodeG n = umovCode (savedG n) 0 := rfl
theorem setMod_eq (n m : Nat) : setMod n m = VG.Impl.Weierstrass.AArch64.setConst n (moAt n) m := rfl

/-- `vg_<curve>_mul_mod_n` for a general modulus: `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mulFnG_ok {n m W : Nat} (hM : ModOkG n m) {s : State} (hp : Pre n W s)
    (hb : wordsVal s.mem (s.gpr .x0) (arg s .x3) n < m) :
    WP isa (mulFnG n m) s fun s' => abiPreserved s s' ∧ Kept n (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) n < m ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) n * 2 ^ (64 * n) % m =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) n * wordsVal s.mem (s.gpr .x0) (arg s .x3) n % m) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d := by
  have R := regsG_ok n hM.hn
  have hn9 : n ≤ 9 := by rcases hM.hn with h | h | h <;> omega_using [h]
  have hn4 : 4 ≤ n := by rcases hM.hn with h | h | h <;> omega_using [h]
  have hown := own_eq hn9
  have hfit := hp.fit
  have hw := hp.w
  have hw8 := hp.w8
  have ho := hp.o
  have ha := hp.a
  have hb' := hp.b
  have k0 := R.keep0 .x0 (by simp)
  obtain ⟨hmo1, hmo2, hmo8⟩ := moAt_facts hn9 hn4
  rw [mulFnG_wp, WP.block_append_iff]
  refine WP.mono (zext_ok s) fun s₁ ⟨g1, g2, g3, K₁, V₁⟩ => ?_
  rw [WP.block_append_iff, saveCodeG_eq]
  refine WP.mono (saves_ok (savedG n) 0 (s := s₁) (by have := R.slen; omega_using [this])) fun s₂ ⟨K₂, L₂, _, V₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ptrsG_ok s₂) fun s₃ ⟨go, ga, gb, K₃, V₃⟩ => ?_
  have x0₂ : s₂.gpr .x0 = s.gpr .x0 := by rw [K₂.gpr, K₁.gpr _ (by decide)]
  have x0₃ : s₃.gpr .x0 = s.gpr .x0 := by rw [K₃.gpr _ (by decide), x0₂]
  have hs₃ : Scr s₃ (s.gpr .x0) W := ⟨x0₃, by rw [K₃.wr, K₂.wr, K₁.wr, hp.wr]; simp, hfit, by omega_using [hw8]⟩
  have off0 : ∀ x : Reg, s₂.gpr x = s₁.gpr x := fun x => by rw [K₂.gpr]
  -- The modulus into the function's own working space.
  rw [WP.block_append_iff]
  have nv := hM.novec
  have hSC := setConst_ok hs₃ (n := n) (o := moAt n) (x := m) (by omega_using [hw]) hmo8 hM.m_lt
  rw [← setMod_eq] at hSC
  refine WP.mono (WP.block_novec (fun i hi => nv i (List.mem_append_right _ (List.mem_append_left _ hi)))
    hSC) fun s₄ ⟨⟨v₄, k₄, O₄⟩, V₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have gk : ∀ r ∈ [raG, rbG, roG, Reg.x0], s₄.gpr r = s₃.gpr r := fun r hr => k₄.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)
  have hP : ∀ (d e : Nat), d + 8 ≤ 8 * n → e + 8 * n ≤ own n →
      InRegions (s₄.rd ++ s₄.wr) (off (s.gpr .x0) e + BitVec.ofNat 64 d) 8 := by
    intro d e hd he
    show InRegions _ (off (off (s.gpr .x0) e) d) 8
    rw [off_off]
    have := hs₄.ld (d := e + d) (by have := hd; have := he; omega)
    rwa [hs₄.x0] at this
  have hpa : Ptr s₄ raG (off (s.gpr .x0) (arg s .x2)) (8 * n) :=
    ⟨by rw [gk raG (by simp), ga, x0₂, off0, g2], fun d hd => hP d _ hd ha, by omega_using [hmo2]⟩
  have hpb : Ptr s₄ rbG (off (s.gpr .x0) (arg s .x3)) (8 * n) :=
    ⟨by rw [gk rbG (by simp), gb, x0₂, off0, g3], fun d hd => hP d _ hd hb', by omega_using [hmo2]⟩
  have hpo : PtrW s₄ roG (off (s.gpr .x0) (arg s .x1)) (8 * n) := by
    refine ⟨by rw [gk roG (by simp), go, x0₂, off0, g1], fun d hd => ?_, by omega_using [hmo2], ?_⟩
    · show InRegions _ (off (off (s.gpr .x0) (arg s .x1)) d) 8
      rw [off_off]
      have := hs₄.st (d := arg s .x1 + d) (by omega_using [hw, ho, hmo1, hd])
      rwa [hs₄.x0] at this
    · simp only [off, Nat.add_comm]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := arg s .x1) (by omega_using [ho, hmo1, hmo2]),
        Nat.mod_eq_of_lt (by omega_using [hn4, hfit, hw, ho, hmo1])]; omega_using [hfit, hw, ho, hmo1]
  have hmem₃ : s₃.mem = s.mem := by rw [K₃.mem, K₂.mem, K₁.mem]
  -- The memory below the modulus is the caller's.
  have ev : ∀ d, d + 8 * n ≤ own n →
      wordsVal s₄.mem (off (s.gpr .x0) d) 0 n = wordsVal s.mem (s.gpr .x0) d n := fun d hd => by
    rw [wordsVal_off, Nat.add_zero, Outside.wordsVal O₄ (Or.inl (by omega_using [hmo1, hd])) (by omega_using [hmo1, hmo2, hd]), hmem₃]
  have hM4 : ModOkW (mod n m) W m s₄.mem (s.gpr .x0) :=
    ⟨by show 0 < n; omega_using [hn4], by show moAt n + 8 * n ≤ W; omega_using [hw],
      by show moAt n - 8 * n + 8 * n ≤ W; omega_using [hw], Or.inr (by show moAt n - 8 * n + 8 * n ≤ moAt n; omega_using [hb', hmo1]),
      v₄, by
        show (m * (BitVec.ofNat 64 (minv m)).toNat + 1) % 2 ^ 64 = 0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (minv_lt m)]; exact hM.inv, hM.red⟩
  have hA : ModA (mod n m) := ⟨hmo8, by show (moAt n - 8 * n) % 8 = 0; omega_using [hmo8]⟩
  have hB : wordsVal s₄.mem (off (s.gpr .x0) (arg s .x3)) 0 n < m := by rw [ev _ hb']; exact hb
  rw [WP.block_append_iff]
  refine WP.mono (WP.block_novec (fun i hi => nv i (List.mem_append_right _ (List.mem_append_right _ hi)))
    (mulR_okW hs₄ hM4 (by show n < 10; omega_using [hn9]) hA hpa hpb hpo R.pa R.pb R.po (o := 0) (a := 0) (b := 0)
      (by show 0 + 8 * n ≤ 8 * n; omega_using []) (by show 0 + 8 * n ≤ 8 * n; omega_using [])
      (by show 0 + 8 * n ≤ 8 * n; omega_using []) rfl rfl rfl hB)) fun s₅ ⟨⟨G₅, V, C⟩, Vv⟩ => ?_
  have hMn : (mod n m).n = n := rfl
  rw [hMn] at G₅ V C
  rw [restoreCodeG_eq]
  refine WP.mono (restores_ok (savedG n) 0 (by have := R.slen; omega_using [this]) R.snd) fun s₆ ⟨K₆, V₆, R₆⟩ => ?_
  have mem₆ : s₆.mem = s₅.mem := K₆.mem
  -- The registers kept by everything but the saves and restores.
  have keep : ∀ r, r ∉ savedG n → r ∉ clob n → r ∉ [raG, rbG, roG, .x1, .x2, .x3] →
      s₆.gpr r = s.gpr r := fun r h1 h2 h3 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h3
    rw [K₆.gpr r h1, G₅.gpr r h2, k₄.gpr r (by simp [h3.2.2.2.1]), K₃.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h3.1, h3.2.1, h3.2.2.1⟩), off0, K₁.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h3.2.2.2.1, h3.2.2.2.2.1, h3.2.2.2.2.2⟩)]
  have vv : s₅.v = s₂.v := by rw [Vv, V₄, V₃]
  refine ⟨⟨fun r hr => ?_, by rw [K₆.sp, G₅.sp, k₄.sp, K₃.sp, K₂.sp, K₁.sp], fun d hd => ?_⟩,
    fun x hx hx' => ?_, ⟨?_, ?_⟩, keep .x0 k0.2.1 k0.1 k0.2.2,
    by rw [K₆.rd, G₅.rd, k₄.rd, K₃.rd, K₂.rd, K₁.rd],
    by rw [K₆.wr, G₅.wr, k₄.wr, K₃.wr, K₂.wr, K₁.wr], fun d hd => by rw [V₆, vv, V₂ d hd, V₁]⟩
  · by_cases hs : r ∈ savedG n
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
      have l := L₂ i hi
      rw [Nat.zero_add] at l
      rw [R₆ i hi, Nat.zero_add, vv, l, K₁.gpr]
      have hp' := R.spres _ (List.getElem_mem hi)
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> rw [h] at hp' <;> exact absurd hp' (by decide)
    · obtain ⟨c1, c2⟩ := R.pres r hr hs
      exact keep r hs c1 c2
  · have hd' : ∀ i < 10, d ≠ (slot i).1 := by
      have : ∀ d ∈ preservedV, ∀ i < 10, d ≠ (slot i).1 := by decide
      exact this d hd
    rw [V₆, vv, V₂ d hd', V₁]
  · rw [mem₆]
    have := Outside.of_off G₅.mem (by omega_using [ho, hmo1, hmo2])
    rw [this x hx, O₄ x hx', hmem₃]
  · have e := wordsVal_off s₅.mem (s.gpr .x0) (arg s .x1) 0 n
    rw [Nat.add_zero] at e
    rw [mem₆, ← e]; exact V
  · have e := wordsVal_off s₅.mem (s.gpr .x0) (arg s .x1) 0 n
    rw [Nat.add_zero] at e
    rw [mem₆, ← e, C, ev _ ha, ev _ hb']

theorem ModOkS.general {n m : Nat} (h : ModOkS n m) : general n m = false := by
  rcases h.kind with ⟨hs, hr⟩ | ⟨hs, ws, hr⟩
  · unfold VG.Impl.Weierstrass.AArch64.Mont.general; rw [hr, hs]; rfl
  · unfold VG.Impl.Weierstrass.AArch64.Mont.general; rw [hr]

theorem sparseOk_of_general {n m : Nat} (h : general n m = true) : sparseOk n m = false := by
  unfold VG.Impl.Weierstrass.AArch64.Mont.general at h
  split at h
  · simpa using h
  · exact absurd h (by decide)

/-- `vg_<curve>_mul_mod_<p|n>`: `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mulFn_ok {n m W : Nat} (hM : ModOk n m) {s : State} (hp : Pre n W s)
    (hb : wordsVal s.mem (s.gpr .x0) (arg s .x3) n < m) :
    WP isa (mulFn n m) s fun s' => abiPreserved s s' ∧ Kept n (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) n < m ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) n * 2 ^ (64 * n) % m =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) n * wordsVal s.mem (s.gpr .x0) (arg s .x3) n % m) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d := by
  rcases hM with hM | hM
  · by_cases hsp : sparseOk n m = true
    · obtain ⟨rfl, rfl⟩ := sparseOk_eq hsp
      simp only [mulFn, hsp, ↓reduceIte]
      exact mulFn384_ok hp hb
    · simp only [mulFn, hsp, hM.general, Bool.false_eq_true, ↓reduceIte]
      exact mulFnS_ok hM hp hb
  · simp only [mulFn, sparseOk_of_general hM.g, hM.g, Bool.false_eq_true, ↓reduceIte]
    exact mulFnG_ok hM hp hb

end VG.Proof.Weierstrass.AArch64.Mont
