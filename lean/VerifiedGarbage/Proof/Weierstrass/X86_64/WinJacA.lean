module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacNorm
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacIter
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
public import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop

/-! ### `Weierstrass.X86_64.WinJacEntryA`, which only this module used -/

section

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
  obtain h4 : 4 ≤ K.M.n := by rcases hL.n46 with h | h <;> omega_using [h]
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
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  have hT : K.T = jg K 80 := hL.T80
  obtain hTl : K.T + 40 * K.M.n ≤ size := by rw [hT]; unfold jg; omega_using [hg]
  have hTt : K.T = K.tbl + 16 * K.st := hL.T
  obtain hr : ∀ e < 16, ∀ c < K.M.n, InRegions (s₁.rd ++ s₁.wr)
      (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 (K.st * e + 16 * c)) 16 := by
    intro e he c hc
    rw [Offset.add_add]
    have := Nat.mul_le_mul_left K.st (show e + 1 ≤ 16 by omega_using [he])
    rw [Nat.mul_succ] at this
    exact ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (by omega_using [hTl, hTt, hc, this]) (by decide)⟩
  -- The pass: the first `n` pieces of the entry.
  obtain hpass : WP isa (.block (if K.avx2 then selPassY K.T 16 K.st ((K.M.n + 1) / 2) (qY K.M.n)
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
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hEz : K.E.z = K.T + 16 * K.M.n := rfl
  refine WP.mono (setConst_ok hs₂ (o := K.E.z) (by rw [hEz]; omega_using [hTl]) hone) fun t ⟨e₃, k₃, O₃⟩ =>
    ⟨fun c hc => ?_, by rw [← hL.Tz]; exact e₃, ?_, ?_⟩
  · have hcn := Nat.mul_le_mul_left K.M.n (show c + 1 ≤ 2 by omega_using [hc])
    rw [Nat.mul_succ] at hcn
    obtain eT : jg K (80 + c) = K.T + 8 * (K.M.n * c) := by
      rw [hT]; unfold jg; rw [Nat.mul_add, ← Nat.mul_assoc]; omega_using []
    rw [eT, O₃.wordsVal (by rw [hEz]; omega_using [hcn]) (by omega_using [ht, hnp, hst, h2n, hTt, hcn])]
    obtain hX : ∀ d, word s₁.mem (base + BitVec.ofNat 64 K.tbl) d = word s.mem base (K.tbl + d) := fun d => by
      rw [k₁.2.1, Mont.word, Mont.word, off, off, Offset.add_add]
    obtain hw : ∀ i < K.M.n, word s₂.mem base (K.T + 8 * (K.M.n * c) + 8 * i) =
        if 1 ≤ a then word s.mem base (jg K (5 * (a - 1) + c) + 8 * i) else 0 := by
      intro i hi
      obtain ⟨c', q, hq, e⟩ : ∃ c' q, q < 2 ∧ K.M.n * c + i = 2 * c' + q :=
        ⟨(K.M.n * c + i) / 2, (K.M.n * c + i) % 2, Nat.mod_lt _ (by decide), by omega_using []⟩
      obtain hc' : c' < K.M.n := by omega_using [hcn, hi, e]
      obtain w := accVal_word1 (a₂ c' hc') hq
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
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) (hF.ro_lt K.P.x (by simp))
  obtain hbits := hf.bits hL hF
  generalize hk' : k + JacWinCfg.offset K.J = k' at hbits
  obtain hwj : 5 * j + 5 ≤ 5 * K.J := by omega_using [hj]
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc hs (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 9; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_using [hbl]) hb hbits) fun s₁ ⟨_, r₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hwin : combWin K.tc.w k' j = Window5.nib k' j := Window5.combWin_five k' j
  have hH : K.tc.H = 16 := rfl
  rw [hwin, hH] at r₁
  generalize ha : magH 16 (Window5.nib k' j) = a at r₁
  obtain ha16 : a ≤ 16 := by rw [← ha]; exact magH_le (by have := Window5.nib_lt k' j; omega_using [this])
  refine WP.mono (jselectA_ok hL hs₁ r₁ ha16 (Nat.lt_trans hone_lt hpn)) fun s₂ ⟨e₂, o₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [m₁] at e₂
  obtain U₂ : Unch base (jwLoopW K) s.mem s₂.mem := by
    rw [← m₁]; exact (outside_grid5 (b := 80) O₂).mono fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  obtain F₂ := hf.next hL hs₂ (((Keeps.regs k₁).mono (sub_powClob (by decide))).trans
    (k₂.mono (sub_powClob (by decide)))) U₂ (jwLoopW_sub K)
  -- The negation.
  obtain ⟨tx, ty, tz, -, -⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  obtain hneg : K.neg ∈ jwSlots K := by jw_mem
  obtain hzero : K.zero ∈ jwSlots K := by jw_mem
  obtain hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by rw [F₂.ro hL (by jw_mem)]; exact hF.zero
  obtain hy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [← ty, e₂ 1 (by decide)]
    split
    · exact (hT a (by omega_arith) ha16).lt 1 (by decide)
    · exact hp0
  obtain hyneg : K.E.y + 8 * K.M.n ≤ K.neg ∨ K.neg + 8 * K.M.n ≤ K.E.y := by
    rw [hL.Ty]; exact (hL.jg_apart (x := K.neg) (by jw_mem) (by decide)).symm
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ F₂.mod (o := K.neg) (a := K.zero) (b := K.E.y) (hL.le hneg) (hL.le hzero)
    (hL.le my) (hL.lay.tmp _ hneg) (hL.lay.tmp _ hzero) (hL.lay.tmp _ my) (hL.lay.mo _ hneg)
    (by rw [hz₂]; exact hp0) hy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  obtain hs₃ := k₃.scr hs₂
  obtain hbits₃ : ∀ t < 5 * K.J, s₃.mem (off base (K.bits + t)) = if k'.testBit t then 1 else 0 := by
    intro t ht
    rw [k₃.unch.byte (fun w hw => by
      obtain hw' : w ∈ jwW K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact mem_jwW_ws (other_ws (by jw_mem))
        · exact mem_jwW_tmp
      have := hL.bits_w w hw'; omega_using [ht, this]) (by omega_using [hn, hbl, ht])]
    have := F₂.bits hL hF t ht; rw [hk'] at this; exact this
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K.tc hs₃ (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 2 ^ 31; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_using [hbl]) (by rw [k₃.gpr _ (rbx_not_clob _), k₂.gpr _ (by decide),
      k₁.1 _ (by decide), hb]) hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [hwin] at x₄
  refine WP.mono (sel_ok (decide (Window5.nib k' j < 2 ^ (K.tc.w - 1))) K.M.n hs₄ x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) (hL.le my) (hL.le my) (hL.le hneg) (Or.inl (Nat.le_refl _))
    (by omega_using [hyneg])) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  obtain hs₅ := hs₄.of_keepRegs k₅ (by decide)
  obtain b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_using [hn, this]
  -- `T`'s words: as at `s₂` but `Y`.
  obtain keepT : ∀ c < 5, c ≠ 1 → wordsVal s₅.mem base (TS K c) K.M.n = wordsVal s₂.mem base (TS K c) K.M.n := by
    intro c hc h1
    obtain hy : TS K c + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ TS K c := by
      rw [hL.Ty]; exact jg_sep K (by omega_using [h1])
    rw [O₅.wordsVal hy (b64 _ (jg_mem (by omega_using [hc]))), m₄, k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact (hL.jg_apart (x := K.neg) (by jw_mem) (i := 80 + c) (by omega_using [hc])).symm
      · exact hL.lay.tmp _ (jg_mem (by omega_using [hc]))) (b64 _ (jg_mem (by omega_using [hc])))]
  obtain y₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hyneg
      · exact hL.lay.tmp _ my) (b64 _ my)
  obtain keepY : wordsVal s₅.mem base (TS K 1) K.M.n = if decide (Window5.nib k' j < 2 ^ (K.tc.w - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [ty, e₅, m₄, e₃, hz₂, y₃]
  obtain tv : ∀ {x y : Nat}, wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base y K.M.n →
      tmv C K.M.n base s₅ x = tmv C K.M.n base s₂ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  obtain hU : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
      [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem s₅.mem := by
    rw [← m₁]
    refine (((outside_grid5 (b := 80) O₂).trans k₃.unch).trans (m₄ ▸ O₅.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (h | h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · rw [h, hL.Ty]; exact Or.inl (List.mem_map.mpr ⟨1, by decide, rfl⟩)
  obtain hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  obtain kk : KeepRegs (clob K.M.n) s s₅ :=
    ((((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      ((⟨k₃.gpr, k₃.rd, k₃.wr⟩ : KeepRegs (clob K.M.n) s₂ s₃).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h])))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  have h16 : (2 : Nat) ^ (K.tc.w - 1) = 16 := rfl
  rw [h16] at keepY
  obtain z₅ : wordsVal s₅.mem base (TS K 2) K.M.n = K.one := by rw [keepT 2 (by decide) (by decide)]; exact o₂
  refine ⟨hf.next hL hs₅ (kk.mono clob_powClob) hU (fun w hw => jwLoopW_sub K w (jent_loopW K w hw)), hU,
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
    obtain J₂ := (hT a h ha16).jac
    obtain ez : tmv C K.M.n base s₅ (TS K 2) = tmv C K.M.n base s (entS K a 2) := by
      show toM _ _ _ = toM _ _ _; rw [z₅, hO a h ha16]
    obtain ex : tmv C K.M.n base s₅ (TS K 0) = tmv C K.M.n base s (entS K a 0) := by
      show toM _ _ _ = toM _ _ _
      rw [keepT 0 (by decide) (by decide), e₂ 0 (by decide), ite_eq_left_of_eq_true _ _ (eq_true h)]
    obtain ey : wordsVal s₂.mem base K.E.y K.M.n = wordsVal s.mem base (entS K a 1) K.M.n := by
      rw [← ty, e₂ 1 (by decide), ite_eq_left_of_eq_true _ _ (eq_true h)]
    rw [Window5.winPt_mag, ha, ex, ez]
    by_cases hng : Window5.nib k' j < 16
    · simp only [decide_eq_true hng, ↓reduceIte]
      simp only [decide_eq_true hng, ↓reduceIte] at keepY
      obtain hy : tmv C K.M.n base s₅ (TS K 1) = -tmv C K.M.n base s (entS K a 1) := by
        show toM _ _ _ = -toM _ _ _
        rw [keepY, toM_sub (by omega_using [hy₂]), toM_zero, ey]
        grind
      rw [hy]; exact J₂.negY
    · simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte]
      simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte] at keepY
      obtain hy : tmv C K.M.n base s₅ (TS K 1) = tmv C K.M.n base s (entS K a 1) := by
        show toM _ _ _ = toM _ _ _; rw [keepY, ey]
      rw [hy]; exact J₂

end VG.Proof.Weierstrass.X86_64

end

end


/-!
# 5-bit windows with an affine table on x86-64

`JacWinCfg.windowA` (`Impl/Weierstrass/X86_64/WinJacA.lean`) leaves `R`
representing `[k]P` in projective coordinates: the table by
`jbuild_ok`, made affine by `normA_ok` (every entry's `Z` one, `JTblOne`),
then the first digit by `jfirst_ok` and the iterations by `jstepA_ok`, which
selects the entry's `X` and `Y` (`jentryA_ok`) and adds it by the mixed addition (`madd_ok`, `jstepA_pt`): right
unless `R = T` (excluded for `k < n` by `Window5.loop_noexc`, as the Jacobian
addition's exceptions) or `R = O` (where `T` is kept, as before).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-! ## The mixed addition -/

/-- `D = R + T` by the mixed addition, `T` affine (its `Z` not read). -/
theorem madd_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s)
    (hV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y], x ∈ V) :
    WP isa (.block (fprog K.M (maddJ K.S K.R K.E K.D))) s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧ ∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.D.x, K.D.y, K.D.z] ++ V) E' t ∧
        (E' K.D.x, E' K.D.y, E' K.D.z) = maddJF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) := by
  have hA := hL.addApart
  obtain hSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ jwSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rw [hL.Tx, hL.Ty, hL.Tz] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact jg_mem (by decide) | jw_mem
  obtain hR : readsOk (maddJ K.S K.R K.E K.D) V = true := by
    rw [maddJ_eq]
    refine readsOk_mono (readsOk_rename (rcbσ K.S K.R K.E K.D)
      (show readsOk maddJN [11, 12, 13, 14, 15] = true by decide)) fun x hx => hV x ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h <;> rw [h] <;> simp [rcbσ, rcbW, rcbR]
  rw [maddJ_eq] at hR ⊢
  refine WP.mono (fprog_ok hL.lay hp _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun t ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, _, hI'.sub fun x hx => ?_, ?_⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out maddJN_ok op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem maddJN_ok hx)
    · exact Or.inl hx
  · exact (congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 6)
      (congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 7) (ofN_run maddJN_ok hA E 8))).trans (maddJN_run _)

/-! ## The point -/

/-- An iteration's result with the mixed addition: `R` for a zero digit, else
`T` where `R = O`, else the mixed sum, a triple of a point of the curve,
`[winE k' J i]P` for `k < n`. -/
theorem jstepA_pt (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {k J i : Nat}
    (hi : i < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {Q1 : Point C} (hQ1 : onCurve C Q1 = true)
    (hQ1e : k < C.n → Q1 = mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P)
    (h1 : InvJ C X1 Y1 Z1 Q1)
    (h2 : 1 ≤ magH 16 (Window5.nib (k + 16 * Window5.geom J) i) →
      InvJ C X2 Y2 Z2 (Window5.winPt C P (k + 16 * Window5.geom J) i) ∧ Z2 = 1) :
    ∃ Q : Point C, onCurve C Q = true ∧ (k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom J) J i) P) ∧
      InvJ C
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then X1
          else if Z1 = 0 then X2 else (maddJF X1 Y1 Z1 X2 Y2).1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Y1
          else if Z1 = 0 then Y2 else (maddJF X1 Y1 Z1 X2 Y2).2.1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Z1
          else if Z1 = 0 then Z2 else (maddJF X1 Y1 Z1 X2 Y2).2.2) Q := by
  obtain hadd := Window5.win_add hC hP (k := k + 16 * Window5.geom J) (J := J) (j := i) (Nat.le_add_left _ _) hi
  obtain noexc : k < C.n → 1 ≤ Window5.winE (k + 16 * Window5.geom J) J (i + 1) →
      mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P ≠
        Window5.winPt C P (k + 16 * Window5.geom J) i := fun hk he =>
    (Window5.loop_noexc hC hO hP hP0 hn17 hn64 hk hi he).1
  generalize k + 16 * Window5.geom J = k' at hadd h2 hQ1e noexc ⊢
  generalize he : Window5.winE k' J (i + 1) = e at hadd hQ1e noexc
  by_cases h0 : magH 16 (Window5.nib k' i) = 0
  · simp only [h0, ↓reduceIte]
    refine ⟨Q1, hQ1, fun hk => ?_, h1⟩
    rw [hQ1e hk, ← hadd, Window5.winPt_zero h0, add_infinity]
  simp only [h0, ↓reduceIte]
  obtain ⟨J2, z2⟩ := h2 (by omega_arith)
  subst z2
  obtain hW := Window5.onCurve_winPt hC hP k' i
  generalize hWe : Window5.winPt C P k' i = W at J2 hW hadd noexc ⊢
  cases W with
  | infinity => exact absurd ((J2.z_zero_iff hC).mpr rfl) hC.one_ne_zero
  | affine x2 y2 =>
  obtain ⟨ex2, ey2⟩ := J2.affine_coords hC
  obtain ex2' : X2 = x2 := by rw [ex2]; grind
  obtain ey2' : Y2 = y2 := by rw [ey2]; grind
  subst ex2' ey2'
  by_cases hz : Z1 = 0
  · simp only [hz, ↓reduceIte]
    refine ⟨_, hW, fun hk => ?_, J2⟩
    rw [← hadd, ← hQ1e hk, (h1.z_zero_iff hC).mp hz, infinity_add']
  simp only [hz, ↓reduceIte]
  by_cases hQW : Q1 = .affine X2 Y2
  · have hZ : (maddJF X1 Y1 Z1 X2 Y2).2.2 = 0 := by
      rw [hQW] at h1
      obtain ⟨hx1, -⟩ := h1.affine_coords hC
      rw [maddJF_z, hx1]; grind
    refine ⟨.infinity, rfl, fun hk => ?_, Or.inl ⟨rfl, hZ⟩⟩
    obtain he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · exact absurd ((h1.z_zero_iff hC).mpr (by rw [hQ1e hk, Nat.mul_zero, Window5.mul_zero_pt])) hz
      · exact h
    exact absurd (by rw [← hQ1e hk]; exact hQW) (noexc hk he1)
  · refine ⟨_, hC.onCurve_add hQ1 hW, fun hk => by rw [← hadd, hQ1e hk], ?_⟩
    exact h1.madd hC hM3 hQ1 hW hz hQW

/-! ## An iteration -/

/-- The loop's invariant: `JInv`, with the table's `Z` one. -/
def JInvA (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k j : Nat) (s : State) : Prop :=
  JInv K C base size P s₀ k j s ∧ JTblOne K base s

theorem JTblOne.loopW (hL : JacWinLay K size) {base : Addr} {s s' : State} (h : JTblOne K base s)
    (hU : Unch base (jwLoopW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64) : JTblOne K base s' :=
  fun m h1 h16 => by
    rw [jgWord_unch hL hU hn (by omega_arith) (loopW_apart hL (by omega_arith))]
    exact h m h1 h16

/-- An iteration, `1 ≤ j ≤ J`: `R = 32 R + [d_{j-1}]P`. -/
theorem jstepA_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) {j : Nat}
    (hj1 : 1 ≤ j) (hjJ : j ≤ K.J) {s : State} (hI : JInvA K C base size P s₀ k j s) :
    WP isa (K.stepA dbl).inline s fun s' => JInvA K C base size P s₀ k (j - 1) s' ∧
      s'.zf = some (decide (j - 1 = 0)) := by
  obtain ⟨hI, hO1⟩ := hI
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, -, -⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  rw [JacWinCfg.stepA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s hj1 (by omega_arith) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain R₁ := R₀.rbxKeeps hL k₁
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dbls_ok hL hC hD hQ (j := j - 1) (by omega_arith) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  obtain O₂ : JTblOne K base s₂ := (show JTblOne K base s₁ from fun m h1 h16 => by
    rw [m₁]; exact hO1 m h1 h16).loopW hL U₂ hn
  refine WP.seq (WP.mono (jentryA_ok hL hF hpn hone_lt (j := j - 1) (by omega_arith) R₂.fr R₂.tbl O₂ b₂) fun s₃ h₃ =>
    WP.seq (WP.mono h₃ fun s₄ E₄ => ?_))
  -- `R` is not written by the entry.
  obtain hRe : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₄.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    obtain hxo : x ∈ jwOther K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
    refine E₄.unch.wordsVal (fun w hw => ?_) (by have := hL.le (other_mem hxo); omega_arith)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      exact hL.jg_apart (List.mem_append_right _ hxo) (by have := List.mem_range.mp hc; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hL.ap_oth (i := 0) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 1) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 2) (j := 6) (by decide) (by decide) (by decide)
      · exact hL.lay.tmp x (other_mem hxo)
  obtain U₄ : Unch base (jwLoopW K) s₂.mem s₄.mem := E₄.unch.mono (jent_loopW K)
  -- `T`'s `Z` is one.
  obtain tz1 : 1 ≤ magH 16 (Window5.nib (k + JacWinCfg.offset K.J) (j - 1)) →
      tmv C K.M.n base s₄ K.E.z = 1 := fun _ => by
    show toM _ _ _ = 1
    rw [← tz, E₄.one, hone]
  -- `D = R + T`.
  obtain V₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y],
      x ∈ jwSlots K ∧ wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact E₄.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact E₄.lt 1 (by decide)⟩
  obtain I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y]
      (tmv C K.M.n base s₄) s₄ :=
    ⟨E₄.fr.scr, E₄.fr.mod, fun x hx => (V₄ x hx).1, fun x hx => (V₄ x hx).2, fun _ _ => rfl⟩
  refine WP.seq (WP.mono (madd_ok hL hp I₄ (fun x hx => hx)) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_)
  obtain U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := k₅.loopW (rcbW_loopW (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem)))
  obtain F₅ := E₄.fr.next hL (k₅.scr E₄.fr.scr) k₅.regs U₅ (jwLoopW_sub K)
  obtain hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (rbx_not_clob _), E₄.keep.gpr _ (rbx_not_clob _), b₂]
  -- `R` and `T` survive the addition.
  obtain keep₅ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₅.mem base x K.M.n = wordsVal s₄.mem base x K.M.n := by
    intro x hx
    obtain hxs : x ∈ jwSlots K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · jw_mem
      · jw_mem
      · jw_mem
      · exact mx
      · exact my
      · exact mz
    refine (ProgKeep.unch k₅).wordsVal (fun w hw => ?_) (by have := hL.le hxs; omega_arith)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
      exact cadd_apart hL x hx y hy
    · rw [List.mem_singleton.mp hw]; exact hL.lay.tmp x hxs
  refine WP.mono (jmask_ok hL hF (i := j - 1) (by omega_arith) F₅ hb₅) fun s₆ ⟨F₆, U₆, b₆, z₆, w₆⟩ => ?_
  rw [offset_eq] at w₆
  have ent := E₄.ent
  rw [offset_eq] at ent tz1
  obtain R5 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base x K.M.n :=
    fun x hx => by
      rw [keep₅ x (List.mem_append_left [K.E.x, K.E.y, K.E.z] hx), hRe x hx]
  obtain T5 : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₅.mem base x K.M.n = wordsVal s₄.mem base x K.M.n :=
    fun x hx => keep₅ x (List.mem_append_right [K.R.x, K.R.y, K.R.z] hx)
  obtain hz : wordsVal s₅.mem base K.R.z K.M.n = 0 ↔ tmv C K.M.n base s₂ K.R.z = 0 := by
    rw [R5 _ (by simp)]; exact (toM_eq_zero_iff hp (R₂.lt _ (by simp))).symm
  obtain Dv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], tmv C K.M.n base s₅ x = E₅ x ∧
      wordsVal s₅.mem base x K.M.n < C.p := fun x hx =>
    ⟨I₅.val x (List.mem_append_left _ hx), I₅.lt x (List.mem_append_left _ hx)⟩
  obtain tvR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      tmv C K.M.n base s₂ x := fun x hx => by rw [R5 x hx]
  obtain tvT : ∀ x ∈ [K.E.x, K.E.y, K.E.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      tmv C K.M.n base s₄ x := fun x hx => by rw [T5 x hx]
  obtain tR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₂ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [hRe x hx]
  rw [tR _ (by simp), tR _ (by simp), tR _ (by simp)] at v₅
  obtain ex : tmv C K.M.n base s₆ K.R.x =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.x
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.x else E₅ K.D.x := by
    obtain w : wordsVal s₆.mem base K.R.x K.M.n = _ := w₆ 0 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.x (by simp)) (tvT K.E.x (by simp)) (Dv K.D.x (by simp)).1
  obtain ey : tmv C K.M.n base s₆ K.R.y =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.y
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.y else E₅ K.D.y := by
    obtain w : wordsVal s₆.mem base K.R.y K.M.n = _ := w₆ 1 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.y (by simp)) (tvT K.E.y (by simp)) (Dv K.D.y (by simp)).1
  obtain ez : tmv C K.M.n base s₆ K.R.z =
      if magH 16 (Window5.nib (k + 16 * Window5.geom K.J) (j - 1)) = 0 then tmv C K.M.n base s₂ K.R.z
      else if tmv C K.M.n base s₂ K.R.z = 0 then tmv C K.M.n base s₄ K.E.z else E₅ K.D.z := by
    obtain w : wordsVal s₆.mem base K.R.z K.M.n = _ := w₆ 2 (by decide)
    show toM _ _ _ = _
    rw [w]
    exact tmv_sel hz (tvR K.R.z (by simp)) (tvT K.E.z (by simp)) (Dv K.D.z (by simp)).1
  obtain vx := congrArg Prod.fst v₅
  obtain vy := congrArg (fun p => p.2.1) v₅
  obtain vz := congrArg (fun p => p.2.2) v₅
  dsimp only at vx vy vz
  rw [vx] at ex; rw [vy] at ey; rw [vz] at ez
  obtain hR := jstepA_pt hC hM3 hO hP hP0 hn17 hn64 (k := k) (i := j - 1) (J := K.J) (by omega_arith)
    (hC.onCurve_mul hQ 32) (fun hk => by
      rw [hQe hk, Window5.mul_mul hC hP, show j - 1 + 1 = j by omega_arith]) R₂.rep
    (Z2 := tmv C K.M.n base s₄ K.E.z) (X2 := tmv C K.M.n base s₄ K.E.x) (Y2 := tmv C K.M.n base s₄ K.E.y)
    (fun h => by
      obtain j1 := ent h
      rw [tx, ty, tz] at j1
      exact ⟨j1, tz1 h⟩)
  obtain ⟨Q', hQ', hQe', hR⟩ := hR
  obtain U₂₆ : Unch base (jwLoopW K) s₂.mem s₆.mem :=
    ((U₄.trans U₅).trans U₆).mono fun w hw => by
      simp only [List.mem_append] at hw; rcases hw with (hw | hw) | hw <;> exact hw
  refine ⟨⟨⟨⟨Q', hQ', hQe', F₆, ((R₂.tbl.loopW hL U₄ hn (by decide)).loopW hL U₅ hn (by decide)).loopW hL U₆ hn
    (by decide), fun x hx => ?_, ?_⟩, b₆⟩, O₂.loopW hL U₂₆ hn⟩, z₆⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have w : wordsVal s₆.mem base K.R.x K.M.n = _ := w₆ 0 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp)]; exact (V₄ _ (by simp)).2
        · exact (Dv _ (by simp)).2
    · have w : wordsVal s₆.mem base K.R.y K.M.n = _ := w₆ 1 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp)]; exact (V₄ _ (by simp)).2
        · exact (Dv _ (by simp)).2
    · have w : wordsVal s₆.mem base K.R.z K.M.n = _ := w₆ 2 (by decide)
      rw [w]; split
      · rw [R5 _ (by simp)]; exact R₂.lt _ (by simp)
      · split
        · rw [T5 _ (by simp), ← tz]; exact E₄.lt 2 (by decide)
        · exact (Dv _ (by simp)).2
  · rw [ex, ey, ez]
    exact hR

/-! ## The window method -/

/-- What the method reads at the start survives what the table's building
and normalization write. -/
theorem JacWinFixed.unchA (hL : JacWinLay K size) {base : Addr} {s s' : State} {P : Point C} {k : Nat}
    {inv : Prog isa} {IW : List (Nat × Nat)} (hI : InvSpecJ K C base size inv IW)
    (hF : JacWinFixed K C base s P k) (hU : Unch base (jwW K ++ IW) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : JacWinFixed K C base s' P k := by
  obtain ro : ∀ x ∈ jwRo K, wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := fun x hx =>
    hU.wordsVal (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hL.ro_w hx w hw
      · rcases hI.w w hw with rfl | rfl | ⟨-, h⟩
        · rw [hL.Tx]; exact hL.jg_apart (List.mem_append_left _ hx) (by decide)
        · exact hL.lay.tmp x (ro_mem hx)
        · exact h x (ro_mem hx)) (by have := hL.le (ro_mem hx); omega_arith)
  obtain tv : ∀ x ∈ jwRo K, tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => tmv_congr (ro x hx)
  refine ⟨⟨by rw [ro _ (by jw_mem)]; exact hF.zero, fun x hx => ?_, ?_, ?_⟩, fun t ht => ?_⟩
  · have hx' : x ∈ jwRo K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> jw_mem
    rw [ro x hx']; exact hF.ro_lt x hx
  · rw [tv _ (by jw_mem), tv _ (by jw_mem), tv _ (by jw_mem)]; exact hF.pt
  · rw [tv _ (by jw_mem)]; exact hF.pz
  · have hb := hL.bits
    rw [hU.byte (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · have := hL.bits_w w hw; omega_arith
      · have := hI.bits w hw; omega_arith) (by omega_arith)]
    exact hF.bits t ht

/-- `[k]P` into `R`, in projective coordinates, for `k` whose bits plus
`offset J` are the table at `K.bits`, if `k < n`, by the window method with
the table made affine, `inv` leaving `R.z^(p-2)` in `E.x`; only `invClob`,
`jwW` and what `inv` writes change. -/
theorem winJacA_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {P : Point C} (hP : onCurve C P = true) {k : Nat}
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) {inv : Prog isa} {IW : List (Nat × Nat)} {base : Addr}
    (hI : InvSpecJ K C base size inv IW) {s₀ : State}
    (hs₀ : Scr s₀ base size) (hM₀ : ModOkW K.M size C.p s₀.mem base) (hF₀ : JacWinFixed K C base s₀ P k) :
    WP isa (K.windowA inv dbl).inline s₀ fun s' => KeepRegs (invClob K.M.n) s₀ s' ∧
      Unch base (jwW K ++ IW) s₀.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hn := hs₀.nowrap
  have hJ := hL.J
  obtain hP0 : P ≠ .infinity := by
    intro h
    have := hF₀.pt
    rw [h, hF₀.pz] at this
    exact hC.one_ne_zero this.2.2
  obtain pc : ∀ r ∈ powClob K.M.n, r ∈ invClob K.M.n := fun r h => List.mem_cons_of_mem _ h
  rw [JacWinCfg.windowA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (jbuild_ok hL hp hC hM3 hO hP hP0 (by omega_arith) hs₀ hM₀ hF₀.toJacWinPt) fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (normA_ok hL hp hC hpn hone_lt hone hI F₁.scr F₁.mod T₁)
    fun s ⟨hs, Kn, Un, hM, T₂, O₂⟩ => ?_)
  obtain U₀ : Unch base (jwW K ++ IW) s₀.mem s.mem := (F₁.unch.trans Un).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢; rcases hw with hw | hw | hw <;> simp [hw]
  obtain hF : JacWinFixed K C base s P k := hF₀.unchA hL hI U₀ hn
  obtain K₀ : KeepRegs (invClob K.M.n) s₀ s := (F₁.keep.mono pc).trans Kn
  refine WP.seq (WP.mono (jfirst_ok hL hC hP hF hkJ (JFrame.refl hs hM) T₂) fun s₂ ⟨I₂, U₂⟩ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInvA K C base size P s k 0 t)
    (Inv := fun j t => JInvA K C base size P s k j t) (n := K.J - 1)
    (fun j t h1 h2 hi => jstepA_ok hL hp hC hM3 hO hD hP hP0 hn17 hn64 hpn hone_lt hone hF h1 (by omega_arith) hi)
    (fun _ h => h) (by omega_arith) ⟨I₂, O₂.loopW hL U₂ hn⟩) fun s₃ ⟨I₃, _⟩ => ?_)
  obtain ⟨Q, -, hQe, R₃⟩ := I₃.st
  rw [Window5.winE_zero'] at hQe
  -- `Y = 1` where `Z = 0`.
  have hs₃ := R₃.fr.scr
  obtain hz₃ : wordsVal s₃.mem base K.zero K.M.n = 0 := by rw [R₃.fr.ro hL (by jw_mem)]; exact hF.zero
  obtain ayz : K.R.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.R.y :=
    hL.ap (by jw_mem) (by jw_mem) (fun e => hL.ro K.zero (by jw_mem) (by rw [← e]; jw_mem))
  refine WP.seq (WP.mono (outFix_ok K.tc hs₃ hL.n0 (Nat.lt_trans hone_lt hpn)
    (show K.R.y + 8 * K.M.n ≤ size from hL.le (by jw_mem)) (show K.R.z + 8 * K.M.n ≤ size from hL.le (by jw_mem))
    (show K.zero + 8 * K.M.n ≤ size from hL.le (by jw_mem)) ayz hz₃) fun s₄ ⟨ey₄', k₄, O₄'⟩ => ?_)
  have ey₄ : wordsVal s₄.mem base K.R.y K.M.n = if wordsVal s₃.mem base K.R.z K.M.n = 0 then K.one
      else wordsVal s₃.mem base K.R.y K.M.n := ey₄'
  have O₄ : Outside base K.R.y (8 * K.M.n) s₃.mem s₄.mem := O₄'
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_arith
  obtain ex₄ : wordsVal s₄.mem base K.R.x K.M.n = wordsVal s₃.mem base K.R.x K.M.n :=
    O₄.wordsVal (hL.ap_oth (i := 0) (j := 1) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  obtain ez₄ : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s₃.mem base K.R.z K.M.n :=
    O₄.wordsVal (hL.ap_oth (i := 2) (j := 1) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  obtain U₄ : Unch base (jwLoopW K) s₃.mem s₄.mem := O₄.unch.mono fun w hw => by
    rw [List.mem_singleton.mp hw]; exact other_loopW (by jw_mem)
  obtain F₄ := R₃.fr.next hL hs₄ (k₄.mono (sub_powClob (by decide))) U₄ (jwLoopW_sub K)
  obtain hlt₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₄]; exact R₃.lt _ (by simp)
    · rw [ey₄]; split
      · exact hone_lt
      · exact R₃.lt _ (by simp)
    · rw [ez₄]; exact R₃.lt _ (by simp)
  obtain hSlR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwSlots K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  obtain I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z] (tmv C K.M.n base s₄) s₄ :=
    ⟨hs₄, F₄.mod, hSlR, hlt₄, fun _ _ => rfl⟩
  obtain hS : ∀ op ∈ K.tc.outOps, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    intro op hop x hx
    simp only [TCombCfg.outOps, JacWinCfg.tc, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;>
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;> jw_mem
  obtain hR : readsOk K.tc.outOps [K.R.x, K.R.y, K.R.z] = true := by
    simp [readsOk, TCombCfg.outOps, FOp.ins, FOp.out, JacWinCfg.tc]
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ I₄ hS hR) fun s₅ ⟨P₅, I₅⟩ => ?_
  obtain hval : ∀ x ∈ [K.R.x, K.R.y, K.R.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      runOps K.tc.outOps (tmv C K.M.n base s₄) x ∧ wordsVal s₅.mem base x K.M.n < C.p := fun x hx => by
    obtain hm : x ∈ validAfter K.tc.outOps [K.R.x, K.R.y, K.R.z] := (mem_validAfter _ _).mpr (Or.inl hx)
    exact ⟨I₅.val x hm, I₅.lt x hm⟩
  obtain U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := P₅.loopW (by
    intro x hx
    simp only [TCombCfg.outOps, JacWinCfg.tc, FOp.out, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem))
  obtain F₅ := F₄.next hL (P₅.scr hs₄) P₅.regs U₅ (jwLoopW_sub K)
  refine ⟨K₀.trans (F₅.keep.mono pc), (U₀.trans F₅.unch).mono fun w hw => by
      simp only [List.mem_append] at hw ⊢; rcases hw with (hw | hw) | hw <;> simp [hw],
    F₅.mod, fun x hx => (hval x hx).2, fun hk => ?_⟩
  obtain e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₅ x = runOps K.tc.outOps (tmv C K.M.n base s₄) x :=
    fun x hx => (hval x hx).1
  rw [e _ (by simp), e _ (by simp), e _ (by simp)]
  obtain hxt : K.R.x ≠ K.S.t0 := hL.oth_ne (i := 0) (j := 7) (by decide) (by decide) (by decide)
  obtain hzt : K.R.z ≠ K.S.t0 := hL.oth_ne (i := 2) (j := 7) (by decide) (by decide) (by decide)
  obtain hxz : K.R.x ≠ K.R.z := hL.oth_ne (i := 0) (j := 2) (by decide) (by decide) (by decide)
  obtain hxy : K.R.x ≠ K.R.y := hL.oth_ne (i := 0) (j := 1) (by decide) (by decide) (by decide)
  obtain hyt : K.R.y ≠ K.S.t0 := hL.oth_ne (i := 1) (j := 7) (by decide) (by decide) (by decide)
  obtain hyz : K.R.y ≠ K.R.z := hL.oth_ne (i := 1) (j := 2) (by decide) (by decide) (by decide)
  simp only [TCombCfg.outOps, JacWinCfg.tc, runOps, List.foldl_cons, List.foldl_nil, FOp.run,
    Function.update_apply, hxt, hzt, hxz, hyt, hyz, hxz.symm, hxt.symm, hxy.symm, ite_true, ite_false]
  obtain hy : tmv C K.M.n base s₄ K.R.y = if tmv C K.M.n base s₃ K.R.z = 0 then 1
      else tmv C K.M.n base s₃ K.R.y := by
    show toM _ _ _ = _
    rw [ey₄]
    by_cases h : wordsVal s₃.mem base K.R.z K.M.n = 0
    · have h' : tmv C K.M.n base s₃ K.R.z = 0 := by show toM _ _ _ = 0; rw [h]; exact toM_zero _ _
      simp only [h, h', ↓reduceIte]; exact hone
    · have h' : tmv C K.M.n base s₃ K.R.z ≠ 0 := fun h0 =>
        h ((toM_eq_zero_iff hp (R₃.lt _ (by simp))).mp h0)
      simp only [h, h', ↓reduceIte]
  obtain ex : tmv C K.M.n base s₄ K.R.x = tmv C K.M.n base s₃ K.R.x := by
    show toM _ _ _ = toM _ _ _; rw [ex₄]
  obtain ez : tmv C K.M.n base s₄ K.R.z = tmv C K.M.n base s₃ K.R.z := by
    show toM _ _ _ = toM _ _ _; rw [ez₄]
  rw [hy, ex, ez, ← hQe hk]
  exact InvJ.out hC R₃.rep

end VG.Proof.Weierstrass.X86_64
