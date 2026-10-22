module

import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacNorm
public import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# 5-bit windows with an affine table on x86-64: the entry of a digit

`JacWinCfg.selectA` selects only the entry's `X` and `Y`, the first `16 n`
bytes of the entry, by `selPassAt_ok` or `selPassYSt_ok` (`jselectA_ok`),
and sets `T`'s `Z` to one, which every entry's is once the table is affine
(`JTblOne`). With `negY`, `T` then holds digit `j`'s point with `Z = 1`
(`jentryA_ok`): what the mixed addition reads.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The selection of an iteration: `T`'s `X` and `Y` are entry `a`'s, or
zero for `a = 0`, and its `Z` is one. -/
theorem jselectA_ok (hL : JacWinLay K size) {s : State} {base : Addr}
    (hs : Scr s base size) {a : Nat} (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (ha : a ≤ 16)
    (hone : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block K.selectA) s fun t =>
      (∀ c < 2, wordsVal t.mem base (jg K (80 + c)) K.M.n =
        if 1 ≤ a then wordsVal s.mem base (jg K (5 * (a - 1) + c)) K.M.n else 0) ∧
      wordsVal t.mem base (jg K 82) K.M.n = K.one ∧
      KeepRegs [.rax, .rcx, .rdx] s t ∧ Outside base (jg K 80) (40 * K.M.n) s.mem t.mem := by
  have hn := hs.nowrap
  have hg := hL.grid_le
  have ht := hL.tbl31
  have h6 := hL.n6
  have h4 : 4 ≤ K.M.n := by rcases hL.n46 with h | h <;> omega_using [h]
  obtain ⟨hnp, hst, h2n⟩ := np16_eq hL
  rw [JacWinCfg.selectA, List.append_assoc, WP.block_append_iff]
  -- `rdx = rdi + tbl`.
  refine WP.mono (show WP isa (.block [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))]) s
      (fun s₁ => s₁.gpr .rdx = base + BitVec.ofNat 64 K.tbl ∧ Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      Option.map_some, imm32_sext ht, hs.rdi, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨x₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  have hT : K.T = jg K 80 := hL.T80
  have hTl : K.T + 40 * K.M.n ≤ size := by rw [hT]; unfold jg; omega_using [hg]
  have hTt : K.T = K.tbl + 16 * K.st := hL.T
  have hr : ∀ e < 16, ∀ c < K.M.n, InRegions (s₁.rd ++ s₁.wr)
      (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 (K.st * e + 16 * c)) 16 := by
    intro e he c hc
    rw [Offset.add_add]
    have := Nat.mul_le_mul_left K.st (show e + 1 ≤ 16 by omega_using [he])
    rw [Nat.mul_succ] at this
    exact ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (by omega_using [hTl, hTt, hc, this]) (by decide)⟩
  -- The pass: the first `n` pieces of the entry.
  have hpass : WP isa (.block (if K.avx2 then selPassY K.T 16 K.st ((K.M.n + 1) / 2) (qY K.M.n)
      else selPassAt K.T 16 K.st K.M.n (16 * ·))) s₁ fun t =>
      (∀ c < K.M.n, t.mem.readW (off base (K.T + 16 * c)) 128 =
        accVal s₁.mem (base + BitVec.ofNat 64 K.tbl) K.st (16 * ·) a 16 c) ∧
      Outside base K.T (16 * K.M.n) s₁.mem t.mem ∧ KeepRegs [.rcx] s₁ t := by
    split
    · exact selPassYSt_ok hs₁ (by omega_using [hnp, h2n]) (by omega_using [hnp, h2n]) (by decide) (by omega_using [ha]) (by omega_using [hst, h2n]) (by omega_using [hnp, hst]) h8₁ x₁
        ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (d := K.tbl) (by omega_using [hTl, hTt]) (by omega_using [hnp, hst])⟩
        (by omega_using [hTl])
    · exact (selPassAt_ok (d := 0) hs₁ (by omega_using [hnp, h2n]) (by decide) (by omega_using [ha]) h8₁ x₁ (fun c _ => by omega_using [])
        hr (by omega_using [hTl])).mono
        fun t ⟨a₂, O₂, k₂⟩ => ⟨fun c hc => by rw [← a₂ c hc, Nat.add_zero], by rw [← Nat.add_zero K.T]; exact O₂, k₂⟩
  rw [WP.block_append_iff]
  refine WP.mono hpass fun s₂ ⟨a₂, O₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hEz : K.E.z = K.T + 16 * K.M.n := rfl
  refine WP.mono (setConst_ok hs₂ (o := K.E.z) (by rw [hEz]; omega_using [hTl]) hone) fun t ⟨e₃, k₃, O₃⟩ =>
    ⟨fun c hc => ?_, by rw [← hL.Tz]; exact e₃, ?_, ?_⟩
  · have hcn := Nat.mul_le_mul_left K.M.n (show c + 1 ≤ 2 by omega_using [hc])
    rw [Nat.mul_succ] at hcn
    have eT : jg K (80 + c) = K.T + 8 * (K.M.n * c) := by
      rw [hT]; unfold jg; rw [Nat.mul_add, ← Nat.mul_assoc]; omega_using []
    rw [eT, O₃.wordsVal (by rw [hEz]; omega_using [hcn]) (by omega_using [ht, hnp, hst, h2n, hTt, hcn])]
    have hX : ∀ d, word s₁.mem (base + BitVec.ofNat 64 K.tbl) d = word s.mem base (K.tbl + d) := fun d => by
      rw [k₁.2.1, Mont.word, Mont.word, off, off, Offset.add_add]
    have hw : ∀ i < K.M.n, word s₂.mem base (K.T + 8 * (K.M.n * c) + 8 * i) =
        if 1 ≤ a then word s.mem base (jg K (5 * (a - 1) + c) + 8 * i) else 0 := by
      intro i hi
      obtain ⟨c', q, hq, e⟩ : ∃ c' q, q < 2 ∧ K.M.n * c + i = 2 * c' + q :=
        ⟨(K.M.n * c + i) / 2, (K.M.n * c + i) % 2, Nat.mod_lt _ (by decide), by omega_using []⟩
      have hc' : c' < K.M.n := by omega_using [hcn, hi, e]
      have w := accVal_word1 (a₂ c' hc') hq
      rw [show K.T + 16 * c' + 8 * q = K.T + 8 * (K.M.n * c) + 8 * i by omega_using [e]] at w
      rw [w]
      by_cases h1 : 1 ≤ a
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩), ite_eq_left_of_eq_true _ _ (eq_true h1), hX]
        congr 1; unfold jg JacWinCfg.st
        rw [show 40 * K.M.n * (a - 1) = 8 * K.M.n * (5 * (a - 1)) by
          rw [Nat.mul_assoc, Nat.mul_assoc, show 40 = 8 * 5 from rfl, Nat.mul_assoc, Nat.mul_left_comm 5],
          Nat.mul_add (8 * K.M.n), Nat.mul_assoc 8 K.M.n c, Nat.mul_assoc 8 K.M.n (5 * (a - 1))]
        omega_using [e]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [h1])), ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      refine wordsVal_congr₂ _ _ _ fun i hi => ?_
      rw [hw i hi, ite_eq_left_of_eq_true _ _ (eq_true h1)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      refine wordsVal_zeros fun i hi => ?_
      rw [hw i hi, ite_eq_right_of_eq_false _ _ (eq_false h1)]
  · refine ⟨fun r hr => ?_, by rw [k₃.rd, k₂.rd, k₁.2.2.1], by rw [k₃.wr, k₂.wr, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₃.gpr r (by simp [hr.1]), k₂.gpr r (by simp [hr.2.1]), k₁.1 r (by simp [hr.2.2])]
  · rw [← hT, ← k₁.2.1]
    exact (O₂.mono (Nat.le_refl _) (by omega_using [])).trans (O₃.mono (by rw [hEz]; omega_using []) (by rw [hEz]; omega_using []))

/-- What `T` holds after an iteration's selection and the negation, from `s`:
`Z` one, and digit `j`'s point for a nonzero digit. -/
structure JEntA (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k' j : Nat) (s t : State) : Prop where
  fr : JFrame K C base size s₀ t
  unch : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
    [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem t.mem
  keep : KeepRegs (clob K.M.n) s t
  lt : ∀ c < 3, wordsVal t.mem base (TS K c) K.M.n < C.p
  one : wordsVal t.mem base (TS K 2) K.M.n = K.one
  ent : 1 ≤ magH 16 (Window5.nib k' j) → InvJ C (tmv C K.M.n base t (TS K 0)) (tmv C K.M.n base t (TS K 1))
    (tmv C K.M.n base t (TS K 2)) (Window5.winPt C P k' j)

/-- `T` holding entry `a`'s `X` and `Y` (zero for `a = 0`), of digit `j`'s
window, and `Z = 1`, its `Y` negated for a negative digit: `T` then holds
digit `j`'s point, as `JEntA` says. -/
theorem jnegA_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) (hone_lt : K.one < C.p) {s s₂ : State} {j : Nat} (hj : j < K.J)
    (hT : JTblOk K C base P 16 s) (hO : JTblOne K base s)
    (F₂ : JFrame K C base size s₀ s₂) (hb : s₂.gpr .rbx = BitVec.ofNat 64 j) {a : Nat}
    (ha : magH 16 (Window5.nib (k + JacWinCfg.offset K.J) j) = a) (ha16 : a ≤ 16)
    (e₂ : ∀ c < 2, wordsVal s₂.mem base (jg K (80 + c)) K.M.n =
      if 1 ≤ a then wordsVal s.mem base (jg K (5 * (a - 1) + c)) K.M.n else 0)
    (o₂ : wordsVal s₂.mem base (jg K 82) K.M.n = K.one) :
    WP isa (.block K.tc.negY) s₂ fun s₅ => JFrame K C base size s₀ s₅ ∧
      Unch base [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)] s₂.mem s₅.mem ∧
      KeepRegs (clob K.M.n) s₂ s₅ ∧ (∀ c < 3, wordsVal s₅.mem base (TS K c) K.M.n < C.p) ∧
      wordsVal s₅.mem base (TS K 2) K.M.n = K.one ∧
      (1 ≤ magH 16 (Window5.nib (k + JacWinCfg.offset K.J) j) →
        InvJ C (tmv C K.M.n base s₅ (TS K 0)) (tmv C K.M.n base s₅ (TS K 1))
          (tmv C K.M.n base s₅ (TS K 2)) (Window5.winPt C P (k + JacWinCfg.offset K.J) j)) := by
  have hs₂ := F₂.scr
  have hn := hs₂.nowrap
  have hbl := hL.bits
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) (hF.ro_lt K.P.x (by simp))
  have hbits := F₂.bits hL hF
  generalize hk' : k + JacWinCfg.offset K.J = k' at hbits ha ⊢
  have hwj : 5 * j + 5 ≤ 5 * K.J := by omega_using [hj]
  have hwin : combWin K.tc.w k' j = Window5.nib k' j := Window5.combWin_five k' j
  -- The negation.
  obtain ⟨tx, ty, tz, -, -⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  have hneg : K.neg ∈ jwSlots K := by jw_mem
  have hzero : K.zero ∈ jwSlots K := by jw_mem
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by rw [F₂.ro hL (by jw_mem)]; exact hF.zero
  have hy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [← ty, e₂ 1 (by decide)]
    split
    · exact (hT a (by omega_arith) ha16).lt 1 (by decide)
    · exact hp0
  have hyneg : K.E.y + 8 * K.M.n ≤ K.neg ∨ K.neg + 8 * K.M.n ≤ K.E.y := by
    rw [hL.Ty]; exact (hL.jg_apart (x := K.neg) (by jw_mem) (by decide)).symm
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ F₂.mod (o := K.neg) (a := K.zero) (b := K.E.y) (hL.le hneg) (hL.le hzero)
    (hL.le my) (hL.lay.tmp _ hneg) (hL.lay.tmp _ hzero) (hL.lay.tmp _ my) (hL.lay.mo _ hneg)
    (by rw [hz₂]; exact hp0) hy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  have hs₃ := k₃.scr hs₂
  have hbits₃ : ∀ t < 5 * K.J, s₃.mem (off base (K.bits + t)) = if k'.testBit t then 1 else 0 := by
    intro t ht
    rw [k₃.unch.byte (fun w hw => by
      have hw' : w ∈ jwW K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact mem_jwW_ws (other_ws (by jw_mem))
        · exact mem_jwW_tmp
      have := hL.bits_w w hw'; omega_using [ht, this]) (by omega_using [hn, hbl, ht])]
    exact hbits t ht
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K.tc hs₃ (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 2 ^ 31; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_using [hbl]) (by rw [k₃.gpr _ (rbx_not_clob _), hb]) hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [hwin] at x₄
  refine WP.mono (sel_ok (decide (Window5.nib k' j < 2 ^ (K.tc.w - 1))) K.M.n hs₄ x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) (hL.le my) (hL.le my) (hL.le hneg) (Or.inl (Nat.le_refl _))
    (by omega_using [hyneg])) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_using [hn, this]
  -- `T`'s words: as at `s₂` but `Y`.
  have keepT : ∀ c < 5, c ≠ 1 → wordsVal s₅.mem base (TS K c) K.M.n = wordsVal s₂.mem base (TS K c) K.M.n := by
    intro c hc h1
    have hy : TS K c + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ TS K c := by
      rw [hL.Ty]; exact jg_sep K (by omega_using [h1])
    rw [O₅.wordsVal hy (b64 _ (jg_mem (by omega_using [hc]))), m₄, k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact (hL.jg_apart (x := K.neg) (by jw_mem) (i := 80 + c) (by omega_using [hc])).symm
      · exact hL.lay.tmp _ (jg_mem (by omega_using [hc]))) (b64 _ (jg_mem (by omega_using [hc])))]
  have y₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hyneg
      · exact hL.lay.tmp _ my) (b64 _ my)
  have keepY : wordsVal s₅.mem base (TS K 1) K.M.n = if decide (Window5.nib k' j < 2 ^ (K.tc.w - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [ty, e₅, m₄, e₃, hz₂, y₃]
  have tv : ∀ {x y : Nat}, wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base y K.M.n →
      tmv C K.M.n base s₅ x = tmv C K.M.n base s₂ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  have hU : Unch base [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)] s₂.mem s₅.mem := by
    refine (k₃.unch.trans (m₄ ▸ O₅.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [h, hL.Ty]; exact Or.inr (Or.inr rfl)
  have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  have kk : KeepRegs (clob K.M.n) s₂ s₅ :=
    ((⟨k₃.gpr, k₃.rd, k₃.wr⟩ : KeepRegs (clob K.M.n) s₂ s₃).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  have h16 : (2 : Nat) ^ (K.tc.w - 1) = 16 := rfl
  rw [h16] at keepY
  have z₅ : wordsVal s₅.mem base (TS K 2) K.M.n = K.one := by rw [keepT 2 (by decide) (by decide)]; exact o₂
  refine ⟨F₂.next hL hs₅ (kk.mono clob_powClob) hU (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact mem_jwW_ws (other_ws (by jw_mem))
      · exact mem_jwW_tmp
      · exact mem_jwW_ws (jg_ws (by decide))), hU,
    kk, fun c hc => ?_, z₅, fun h => ?_⟩
  · by_cases h1 : c = 1
    · subst h1; rw [keepY]; split
      · exact Nat.mod_lt _ hp0
      · exact hy₂
    · by_cases h2 : c = 2
      · subst h2; rw [z₅]; exact hone_lt
      · have hc0 : c = 0 := by omega_using [hc, h1, h2]
        subst hc0
        rw [keepT 0 (by decide) (by decide), e₂ 0 (by decide)]; split
        · exact (hT a ‹_› ha16).lt 0 (by decide)
        · exact hp0
  · rw [ha] at h
    have J₂ := (hT a h ha16).jac
    have ez : tmv C K.M.n base s₅ (TS K 2) = tmv C K.M.n base s (entS K a 2) := by
      show toM _ _ _ = toM _ _ _; rw [z₅, hO a h ha16]
    have ex : tmv C K.M.n base s₅ (TS K 0) = tmv C K.M.n base s (entS K a 0) := by
      show toM _ _ _ = toM _ _ _
      rw [keepT 0 (by decide) (by decide), e₂ 0 (by decide), ite_eq_left_of_eq_true _ _ (eq_true h)]
    have ey : wordsVal s₂.mem base K.E.y K.M.n = wordsVal s.mem base (entS K a 1) K.M.n := by
      rw [← ty, e₂ 1 (by decide), ite_eq_left_of_eq_true _ _ (eq_true h)]
    rw [Window5.winPt_mag, ha, ex, ez]
    by_cases hng : Window5.nib k' j < 16
    · simp only [decide_eq_true hng, ↓reduceIte]
      simp only [decide_eq_true hng, ↓reduceIte] at keepY
      have hy : tmv C K.M.n base s₅ (TS K 1) = -tmv C K.M.n base s (entS K a 1) := by
        show toM _ _ _ = -toM _ _ _
        rw [keepY, toM_sub (by omega_using [hy₂]), toM_zero, ey]
        grind
      rw [hy]; exact J₂.negY
    · simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte]
      simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte] at keepY
      have hy : tmv C K.M.n base s₅ (TS K 1) = tmv C K.M.n base s (entS K a 1) := by
        show toM _ _ _ = toM _ _ _; rw [keepY, ey]
      rw [hy]; exact J₂


/-- Digit `j`'s affine entry into `T`, negated for a negative digit. -/
theorem jentryA_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    {s : State} {j : Nat} (hj : j < K.J)
    (hf : JFrame K C base size s₀ s) (hT : JTblOk K C base P 16 s) (hO : JTblOne K base s)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (K.tc.digit ++ K.selectA)) s fun s₂ =>
      WP isa (.block K.tc.negY) s₂ (JEntA K C base size P s₀ (k + JacWinCfg.offset K.J) j s) := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hbl := hL.bits
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) (hF.ro_lt K.P.x (by simp))
  have hbits := hf.bits hL hF
  generalize hk' : k + JacWinCfg.offset K.J = k' at hbits
  have hwj : 5 * j + 5 ≤ 5 * K.J := by omega_using [hj]
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc hs (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 9; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_using [hbl]) hb hbits) fun s₁ ⟨_, r₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hwin : combWin K.tc.w k' j = Window5.nib k' j := Window5.combWin_five k' j
  have hH : K.tc.H = 16 := rfl
  rw [hwin, hH] at r₁
  generalize ha : magH 16 (Window5.nib k' j) = a at r₁
  have ha16 : a ≤ 16 := by rw [← ha]; exact magH_le (by have := Window5.nib_lt k' j; omega_using [this])
  refine WP.mono (jselectA_ok hL hs₁ r₁ ha16 (Nat.lt_trans hone_lt hpn)) fun s₂ ⟨e₂, o₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [m₁] at e₂
  have U₂ : Unch base (jwLoopW K) s.mem s₂.mem := by
    rw [← m₁]; exact (outside_grid5 (b := 80) O₂).mono fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  have F₂ := hf.next hL hs₂ (((Keeps.regs k₁).mono (sub_powClob (by decide))).trans
    (k₂.mono (sub_powClob (by decide)))) U₂ (jwLoopW_sub K)
  have hU₂ : Unch base ((List.range 5).map fun c => (jg K (80 + c), 8 * K.M.n)) s.mem s₂.mem := by
    rw [← m₁]; exact outside_grid5 (b := 80) O₂
  rw [← hk'] at ha
  refine WP.mono (jnegA_ok hL hF hone_lt hj hT hO F₂ (by rw [k₂.gpr _ (by decide), k₁.1 _ (by decide), hb]) ha ha16
    e₂ o₂) fun s₅ ⟨F₅, U₅, kk₅, lt₅, one₅, ent₅⟩ => ⟨F₅, ?_, ?_, lt₅, one₅, by rw [← hk']; exact ent₅⟩
  · refine (hU₂.trans U₅).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · rw [h]; exact Or.inl (List.mem_map.mpr ⟨1, by decide, rfl⟩)
  · have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simp [clob]
      · simp [clob]
      · simp [clob]
      · exact r8_mem_clob _
    exact (((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans kk₅

end VG.Proof.Weierstrass.X86_64
