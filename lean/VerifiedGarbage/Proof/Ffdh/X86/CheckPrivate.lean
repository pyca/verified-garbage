module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublic
public import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# `vg_ffdh_check_private` on i686: the checks

`front_ok`: ZF tells whether x is an invalid scalar (`privateValid`, for
any domain: below q, or without q below `p − 1`, which for a p of zero is
also below p). `body_ok`: for a valid domain, the status is
`privateStatus`: 2 for an invalid scalar, else 1 exactly when
`1 < y < p − 1` and `g^x mod p = y`; a power of the checked generator is in
its subgroup (`publicValid_power`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckPrivate

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes argNum_comp)
open VG.Proof.Ffdh.X86.CheckPublic (YGeo yv loadY_ok bytes_keep)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len dlen xl : Nat}
  {args : Nat → BitVec 32}

/-- x, of `xl` bytes at synthetic argument 10, with its length at 11. -/
structure XGeo (args : Nat → BitVec 32) (base : Addr) (bytes len xl : Nat) (rd wr : List Region) : Prop where
  e11 : args 11 = BitVec.ofNat 32 xl
  pos : 0 < xl
  le : xl ≤ len
  fit : (args 10).toNat + xl ≤ 2 ^ 32
  rd : InRegions (rd ++ wr) (byteAddr (args 10)) xl
  apart : Region.Disjoint ⟨byteAddr (args 10), xl⟩ ⟨base, bytes⟩

theorem XGeo.keep {rd wr : List Region} (X : XGeo args base bytes len xl rd wr) {s t : State} {rs : List Reg}
    (e : s.rd = rd ∧ s.wr = wr) (K : Keeps rs s t) : XGeo args base bytes len xl t.rd t.wr := by
  rw [K.2.1, K.2.2, e.1, e.2]; exact X

/-- x's value. -/
abbrev xv (m : Mem) (args : Nat → BitVec 32) (xl : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 10)) xl)

/-- x into the wide slot 13. -/
theorem loadX_ok (h : In Ex base bytes len args s) (X : XGeo args base bytes len xl s.rd s.wr) :
    WP isa (load (.slot .wide 13) (one .wide) 10 11) s fun u =>
      sv u.mem base len .wide 13 = xv s.mem args xl ∧
      Outside base (lo len (.slot .wide 13)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have lb := len_le_bc len
  have := X.le
  refine WP.mono (load_ok h (one_ok .wide) (slot_fit1 h (j := 13) (by decide)) (p := 10) (l := 11) (L := xl)
    (by decide) (by decide) X.e11 X.pos (by rw [cb1]; omega) X.fit X.rd X.apart)
    fun u ⟨V, O, K⟩ => ⟨by rw [cw1] at V; exact V, by rw [cb1] at O; exact O, K⟩

/-- A copy of the wide slot 15 into 16. -/
theorem copy1516_ok (h : In Ex base bytes len args s) :
    WP isa (copy (.slot .wide 15) (.slot .wide 16) (one .wide)) s fun u =>
      Outside base (lo len (.slot .wide 16)) (bc len .wide) s.mem u.mem ∧
      sv u.mem base len .wide 16 = sv s.mem base len .wide 15 ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e15 := lo_wide len 15
  have e16 := lo_wide len 16
  refine WP.mono (copy_ok h (x := .slot .wide 15) (d := .slot .wide 16) (one_ok .wide) (slot_fit1 h (by decide))
    (slot_fit1 h (by decide)) (by rw [cb1]; exact .inr (by omega))) fun u ⟨O, V, K⟩ => ⟨?_, ?_, K⟩
  · rw [cb1] at O; exact O
  · rw [cw1] at V; exact V

/-- The scalar's bound in slot 16, and in the accumulator word whether, without q, x is below p. -/
theorem bound_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    {A x p qv : Nat} (h15 : sv s.mem base len .wide 15 = A) (h13 : sv s.mem base len .wide 13 = x)
    (h9 : sv s.mem base len .wide 9 = p) (hq : ¬ dlen = 2 * len → comp s.mem args len 2 = qv) :
    WP isa Impl.Ffdh.X86.CheckPrivate.bound s fun v => Step Ex base bytes len args s v ∧
      sv v.mem base len .wide 16 = (if dlen = 2 * len then A else qv) ∧
      w32 v.mem base accOff = (cmask (if dlen = 2 * len then decide (x < p) else true)).toNat ∧
      Kept base len [16] [accOff] s.mem v.mem := by
  have dl := G.dl
  have lw := G.lower
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  unfold Impl.Ffdh.X86.CheckPrivate.bound
  refine WP.seq (WP.mono (qTest_ok h G.e3 G.e12 dl) fun u₁ ⟨z₁, m₁, K₁⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u₁ := Step.regs h m₁ K₁
  refine WP.ite _ z₁ (fun hb => ?_) (fun hb => ?_)
  · have e2 : dlen = 2 * len := by simpa using hb
    refine WP.seq (WP.mono (copy1516_ok S₁.inp) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
    have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot S₁.inp (by decide) O₂ K₂
    have k₂ := kept_slot S₁.inp (a := 16) O₂
    refine WP.seq (WP.mono (lessW_ok S₂.inp (a := 13) (b := 9) (by decide) (by decide)) fun u₃ ⟨m₃, e₃, K₃⟩ => ?_)
    have S₃ : Step Ex base bytes len args u₂ u₃ := Step.regs S₂.inp m₃ K₃
    rw [k₂.slot_eq, k₂.slot_eq, m₁, h13, h9] at e₃
    refine WP.mono (storeMask_ok S₃.inp (d := accOff) (by omega) e₃) fun v ⟨_, O₄, W₄, _, K₄⟩ => ?_
    have S₄ : Step Ex base bytes len args u₃ v := Step.word S₃.inp (by omega) O₄ K₄
    have k₄ := kept_word S₃.inp (d := accOff) (by omega) (by decide) O₄
    refine ⟨((S₁.trans S₂).trans S₃).trans S₄, ?_, ?_, ?_⟩
    · simp only [e2, ↓reduceIte]; rw [k₄.slot_eq, m₃, V₂, m₁, h15]
    · simp only [e2, ↓reduceIte]; exact W₄
    · refine ⟨fun j a b c => ?_, fun d a b e c => ?_⟩
      · rw [k₄.slots j a b (by simp), m₃, k₂.slots j a b c, m₁]
      · rw [k₄.words d a b e c, m₃, k₂.words d a b e (by simp), m₁]
  · have e3 : dlen = 3 * len := by
      have : ¬ dlen = 2 * len := by simpa using hb
      omega
    refine WP.seq (WP.mono (loadComp_ok S₁.inp (G.keep ⟨rfl, rfl⟩ S₁.keeps) (k := 2) (j := 16) (by decide)
      (by omega) (by decide)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
    have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot S₁.inp (by decide) O₂ K₂
    have k₂ := kept_slot S₁.inp (a := 16) O₂
    refine wp_movS rfl fun u₃ U₃ _ => ?_
    have S₃ : Step Ex base bytes len args u₂ u₃ := Step.regs S₂.inp U₃.mem U₃.keeps
    refine WP.mono (storeMask_ok S₃.inp (d := accOff) (c := true) (by omega) (by rw [U₃.gpr]; rfl))
      fun v ⟨_, O₄, W₄, _, K₄⟩ => ?_
    have S₄ : Step Ex base bytes len args u₃ v := Step.word S₃.inp (by omega) O₄ K₄
    have k₄ := kept_word S₃.inp (d := accOff) (by omega) (by decide) O₄
    have n2 : ¬ dlen = 2 * len := by omega
    refine ⟨((S₁.trans S₂).trans S₃).trans S₄, ?_, ?_, ?_⟩
    · simp only [n2, ↓reduceIte]; rw [k₄.slot_eq, U₃.mem, V₂, m₁, hq n2]
    · simp only [n2, ↓reduceIte]; exact W₄
    · refine ⟨fun j a b c => ?_, fun d a b e c => ?_⟩
      · rw [k₄.slots j a b (by simp), U₃.mem, k₂.slots j a b c, m₁]
      · rw [k₄.words d a b e c, U₃.mem, k₂.words d a b e (by simp), m₁]

/-- The body up to its branch on the scalar. -/
abbrev privFront : List (Prog isa) :=
  [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5, load (.slot .wide 12) (one .wide) 8 9,
    load (.slot .wide 13) (one .wide) 10 11, Impl.Ffdh.X86.CheckPrivate.bound, Impl.Ffdh.X86.CheckPrivate.scalarMask,
    Impl.Ffdh.X86.testMask]

theorem body_eq : Impl.Ffdh.X86.CheckPrivate.body =
    Prog.chain privFront (.ite .e (Impl.Ffdh.X86.ret 2) Impl.Ffdh.X86.CheckPrivate.pair) := rfl

/-- The parameters of the domain. -/
abbrev params (m : Mem) (args : Nat → BitVec 32) (len dlen : Nat) : Spec.Ffdh.Parameters :=
  Spec.Ffdh.domainOf len (domBytes m args dlen)

/-- The code's scalar test is `privateValid`'s, for any domain. -/
theorem scalar_iff {p q x : Nat} {a : Spec.Ffdh.Parameters} (hp : a.p = p) {dlen : Nat}
    (hq : a.q = if dlen = 2 * len then none else some q) :
    (!((decide (x < (if dlen = 2 * len then pm1 len p else q)) && decide (0 < x)) &&
      (if dlen = 2 * len then decide (x < p) else true))) = true ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.privateValid
  rw [hp, hq]
  by_cases e : dlen = 2 * len
  · simp only [e, ↓reduceIte, Option.getD_none]
    unfold pm1
    by_cases a1 : 0 < x <;> by_cases a2 : x < p - 1 <;> by_cases a3 : x < p <;> by_cases a4 : 0 < p <;>
      simp [a1, a2, a3, a4] <;> omega
  · simp only [e, ↓reduceIte, Option.getD_some, Bool.and_true]
    by_cases a1 : 0 < x <;> by_cases a2 : x < q <;> simp [a1, a2]

/-- p, g, y, x and one into slots 9, 10, 12, 13 and 14, `pm1 p` into 15, and ZF telling whether x is an
invalid scalar. -/
theorem front_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (Y : YGeo args base bytes len s.rd s.wr) (X : XGeo args base bytes len xl s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 40))
    (hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below (s.gpr .esp) 40))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 40)) :
    WP isa (Prog.chain privFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      Gate u (Spec.Ffdh.privateValid (params s.mem args len dlen) (xv s.mem args xl) = false) ∧
      sv u.mem base len .wide 9 = comp s.mem args len 0 ∧ sv u.mem base len .wide 10 = comp s.mem args len 1 ∧
      sv u.mem base len .wide 12 = yv s.mem args len ∧ sv u.mem base len .wide 13 = xv s.mem args xl ∧
      sv u.mem base len .wide 14 = 1 ∧ sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have yf := Y.fit
  have xf := X.fit
  have xle := X.le
  have h2 : 2 * len ≤ dlen := by omega
  have hpa := comp_p s.mem args h2
  have hqa : (params s.mem args len dlen).q = if dlen = 2 * len then none else some (comp s.mem args len 2) := by
    rcases dl with e | e
    · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega)
    · have : ¬ 3 * len = 2 * len := by omega
      simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
  have mo : maskOff = 12 := rfl
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  generalize hP : comp s.mem args len 0 = p at hpa
  generalize hG : comp s.mem args len 1 = g
  generalize hY : yv s.mem args len = y
  generalize hX : xv s.mem args xl = x
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [argNum_comp, hP] at V9 V15
  have S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  -- g, y and x.
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega)
    (by decide)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  rw [comp_keep h G hb40 F₁ (by omega), hG] at V₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot I₁ (by decide) O₂ K₂
  have k₂ := kept_slot I₁ (a := 10) O₂
  have S₁₂ := S₁.trans S₂
  refine WP.seq (WP.mono (loadY_ok S₂.inp (Y.keep ⟨rfl, rfl⟩ S₁₂.keeps)) fun u₃ ⟨V₃, O₃, K₃⟩ => ?_)
  rw [show yv u₂.mem args len = y by rw [yv, bytes_keep h Y.apart (by omega) hy40 S₁₂.frame]; exact hY] at V₃
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.slot S₂.inp (by decide) O₃ K₃
  have k₃ := kept_slot S₂.inp (a := 12) O₃
  have S₁₃ := S₁₂.trans S₃
  refine WP.seq (WP.mono (loadX_ok S₃.inp (X.keep ⟨rfl, rfl⟩ S₁₃.keeps)) fun u₄ ⟨V₄, O₄, K₄⟩ => ?_)
  rw [show xv u₃.mem args xl = x by rw [xv, bytes_keep h X.apart (by omega) hx40 S₁₃.frame]; exact hX] at V₄
  have S₄ : Step Ex base bytes len args u₃ u₄ := Step.slot S₃.inp (by decide) O₄ K₄
  have k₄ := kept_slot S₃.inp (a := 13) O₄
  have S₁₄ := S₁₃.trans S₄
  have k₁₄ : Kept base len [9, 10, 12, 13, 14, 15] [] s.mem u₄.mem :=
    ((k₁.mono).trans k₂.mono).trans (k₃.mono.trans k₄.mono)
  have v9 : sv u₄.mem base len .wide 9 = p := by rw [k₄.slot_eq, k₃.slot_eq, k₂.slot_eq, V9]
  have v10 : sv u₄.mem base len .wide 10 = g := by rw [k₄.slot_eq, k₃.slot_eq, V₂]
  have v12 : sv u₄.mem base len .wide 12 = y := by rw [k₄.slot_eq, V₃]
  have v14 : sv u₄.mem base len .wide 14 = 1 := by rw [k₄.slot_eq, k₃.slot_eq, k₂.slot_eq, V14]
  have v15 : sv u₄.mem base len .wide 15 = pm1 len p := by rw [k₄.slot_eq, k₃.slot_eq, k₂.slot_eq, V15]
  -- The bound.
  refine WP.seq (WP.mono (bound_ok S₄.inp (G.keep ⟨rfl, rfl⟩ S₁₄.keeps) v15 V₄ v9
    (fun n2 => comp_keep h G hb40 S₁₄.frame (by omega))) fun u₅ ⟨S₅, B₅, W₅, k₅⟩ => ?_)
  -- The scalar's mask.
  refine WP.seq ?_
  unfold Impl.Ffdh.X86.CheckPrivate.scalarMask
  refine WP.seq (WP.mono (zeroW_ok S₅.inp (a := 17) (by decide)) fun u₆ ⟨O₆, Z₆, K₆⟩ => ?_)
  have S₆ : Step Ex base bytes len args u₅ u₆ := Step.slot S₅.inp (by decide) O₆ K₆
  have k₆ := kept_slot S₅.inp (a := 17) O₆
  refine WP.seq (WP.mono (lessW_ok S₆.inp (a := 17) (b := 13) (by decide) (by decide)) fun u₇ ⟨m₇, e₇, K₇⟩ => ?_)
  rw [Z₆, k₆.slot_eq, k₅.slot_eq, V₄] at e₇
  have S₇ : Step Ex base bytes len args u₆ u₇ := Step.regs S₆.inp m₇ K₇
  refine WP.seq (WP.mono (storeMask_ok S₇.inp (d := maskOff) (by omega) e₇) fun u₈ ⟨_, O₈, W₈, _, K₈⟩ => ?_)
  have S₈ : Step Ex base bytes len args u₇ u₈ := Step.word S₇.inp (by omega) O₈ K₈
  have k₈ := kept_word S₇.inp (d := maskOff) (by omega) (by decide) O₈
  refine WP.seq (WP.mono (lessW_ok S₈.inp (a := 13) (b := 16) (by decide) (by decide)) fun u₉ ⟨m₉, e₉, K₉⟩ => ?_)
  rw [k₈.slot_eq, k₈.slot_eq, m₇, k₆.slot_eq, k₆.slot_eq, B₅, k₅.slot_eq, V₄] at e₉
  have S₉ : Step Ex base bytes len args u₈ u₉ := Step.regs S₈.inp m₉ K₉
  have Wacc : w32 u₉.mem base accOff = (cmask (if dlen = 2 * len then decide (x < p) else true)).toNat := by
    rw [m₉, k₈.word_eq, m₇, k₆.word_eq, W₅]
  refine (show WP isa (.block ([.alu .and .ecx (.mem (sc maskOff))] ++ [.alu .and .ecx (.mem (sc accOff))])) u₉ _
    from WP.block_append (WP.mono (andMask_ok S₉.inp (d := maskOff) (c' := decide (0 < x)) (by omega) e₉ (by rw [m₉]; exact W₈))
      fun u₁₀ ⟨e₁₀, m₁₀, K₁₀⟩ => WP.mono (andMask_ok (S₉.inp.regs K₁₀ m₁₀) (d := accOff)
        (c' := if dlen = 2 * len then decide (x < p) else true) (by omega) e₁₀
        (by rw [m₁₀]; exact Wacc)) fun u₁₁ ⟨e₁₁, m₁₁, K₁₁⟩ => ?_))
  have S₁₀ : Step Ex base bytes len args u₉ u₁₀ := Step.regs S₉.inp m₁₀ K₁₀
  have S₁₁ : Step Ex base bytes len args u₁₀ u₁₁ := Step.regs S₁₀.inp m₁₁ K₁₁
  refine WP.seq (WP.mono (testMask_ok e₁₁) fun u₁₂ ⟨z, m₁₂, K₁₂⟩ => WP.block_nil ?_)
  have S₁₂ : Step Ex base bytes len args u₁₁ u₁₂ := Step.regs S₁₁.inp m₁₂ K₁₂
  have S := (((((((S₁₄.trans S₅).trans S₆).trans S₇).trans S₈).trans S₉).trans S₁₀).trans S₁₁).trans S₁₂
  have kk : ∀ {j}, 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [16, 17] →
      sv u₁₂.mem base len .wide j = sv u₄.mem base len .wide j := by
    intro j hj
    have h16 : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [16] := ⟨hj.1, hj.2.1, by simp at hj ⊢; omega⟩
    have h17 : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [17] := ⟨hj.1, hj.2.1, by simp at hj ⊢; omega⟩
    have h0 : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ ([] : List Nat) := ⟨hj.1, hj.2.1, by simp⟩
    rw [m₁₂, m₁₁, m₁₀, m₉, k₈.slot_eq h0, m₇, k₆.slot_eq h17, k₅.slot_eq h16]
  refine ⟨S, Gate.of_eval z (scalar_iff hpa.symm hqa), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kk (by decide), v9]
  · rw [kk (by decide), v10]
  · rw [kk (by decide), v12]
  · rw [kk (by decide), V₄]
  · rw [kk (by decide), v14]
  · rw [kk (by decide), v15]

end VG.Proof.Ffdh.X86.CheckPrivate
