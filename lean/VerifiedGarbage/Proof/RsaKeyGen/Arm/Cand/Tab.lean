module
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Instr
public import VerifiedGarbage.Proof.RsaKeyGen.Table32
import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # A candidate on ARMv7: the table of small primes written (`table_ok`)

`tabWrite a k` stores the words `a` to `a + k − 1` of the table, from a
`movw` and a `movt` each (`tabSteps_ok`); `table_ok`: the first 256 words,
and the other 256 for `w > 16`, over the key arrays 22–48 (`tabJs`), which
nothing else holds then.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

/-- The arrays the table is written over. -/
def tabJs : List Nat := List.range' 22 27

/-- The table's words: 256, or 512 for `W ≥ 35` (`w > 16`). -/
def nT (W : Nat) : Nat := if 35 ≤ W then 512 else 256

export VG.Proof.RsaKeyGen (tabWord32_lo tabWord32_hi tabWord32_lt)

theorem tab_movt {j : Nat} (hj : j < 512) :
    (BitVec.ofNat 16 (tabEntry (2 * j + 1)) ++
      ((BitVec.ofNat 16 (tabEntry (2 * j))).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 (tabWord32 j) := by
  have e0 := (tabEntry_facts (i := 2 * j) (by omega)).2.2
  have e1 := (tabEntry_facts (i := 2 * j + 1) (by omega)).2.2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  unfold tabWord32
  omega

theorem wp_movt' {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- The words `a` to `a + k − 1` of the table, at offset `o` (in `r12`). -/
theorem tabSteps_ok {s : State} {B : BitVec 32} {Z W N : Nat} (hw : Ws s B Z W N) {o a : Nat}
    (r12 : s.gpr .r12 = B + BitVec.ofNat 32 o) :
    ∀ k, a + k ≤ 512 → o + 4 * (a + k) ≤ Z →
    WP isa (.block (tabWrite a k)) s fun s' =>
      (∀ j < k, w32 s'.mem (State.addr B) (o + 4 * (a + j)) = tabWord32 (a + j)) ∧ Rest [.r1] s s' ∧
      Outside (State.addr B) (o + 4 * a) (4 * k) s.mem s'.mem
  | 0, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk, hz => by
    have hn := hw.nowrap
    rw [tabWrite, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (tabSteps_ok hw r12 k (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    simp only [tabStore]
    refine wp_movw fun s₂ u₂ => wp_movt' fun s₃ u₃ => ?_
    have k₃ : Rest [.r1] s s₃ := k₁.trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
    have hw₃ := hw.rest k₃
    have ea : State.addr (s₃.gpr .r12 + BitVec.ofNat 32 (4 * (a + k))) =
        off (State.addr B) (o + 4 * (a + k)) := by
      rw [k₃.gpr _ (by decide), r12, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hw.addr (by omega)
    refine wp_str (by omega) ea (hw₃.write (by omega)) fun s₄ m₄ => WP.block_nil ?_
    have O₂ : Outside (State.addr B) (o + 4 * (a + k)) 4 s₁.mem s₄.mem := by
      rw [m₄.mem, u₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₃.trans (m₄.rest _),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₄.mem, u₃.mem, u₂.mem, w32_write_self, u₃.gpr, u₂.gpr, tab_movt (by omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (tabWord32_lt (by omega))]

/-- Memory that changed only within the arrays `a` to `a + k − 1`. -/
theorem keep_span {B : BitVec 32} {w a k o n : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside (State.addr B) o n m m') (ho : arr w a ≤ o) (hn : o + n ≤ arr w (a + k))
    (hjs : ∀ j, a ≤ j → j < a + k → j ∈ js) : Keep B w js ds m m' := by
  intro x hx
  refine h x ?_
  by_contra hc
  have hS : 0 < S w := by simp only [S]; omega
  have hlo : hdr ≤ ofs (State.addr B) x := by
    have : hdr ≤ arr w a := Nat.le_add_right _ _
    omega
  obtain ⟨q, r, hr, hq⟩ : ∃ q r, r < S w ∧ ofs (State.addr B) x = hdr + q * S w + r :=
    ⟨(ofs (State.addr B) x - hdr) / S w, (ofs (State.addr B) x - hdr) % S w, Nat.mod_lt _ hS, by
      have := Nat.div_add_mod (ofs (State.addr B) x - hdr) (S w)
      rw [Nat.mul_comm] at this; omega⟩
  have h1 : a * S w < (q + 1) * S w := by
    have : arr w a = hdr + a * S w := rfl
    rw [Nat.add_mul]; omega
  have h2 : q * S w < (a + k) * S w := by
    have : arr w (a + k) = hdr + (a + k) * S w := rfl
    omega
  have qa := Nat.lt_of_mul_lt_mul_right h1
  have qk := Nat.lt_of_mul_lt_mul_right h2
  have := hx (arr w q, S w) (by
    simp only [ranges, List.mem_append, List.mem_map]
    exact .inl ⟨q, hjs q (by omega) qk, rfl⟩)
  simp only [arr] at this
  omega

theorem tabJs_mem {j : Nat} (h1 : 22 ≤ j) (h2 : j < 22 + 27) : j ∈ tabJs := by
  simp only [tabJs, List.mem_range'_1]; omega

theorem nT_le {W : Nat} (hw : 10 ≤ W) : aTab * 4 * (W + 2) + 4 * nT W ≤ 49 * (4 * (W + 2)) := by
  simp only [nT, aTab]; split <;> omega

/-- The table: its first `nT W` words at the key array 22, written over the
arrays `tabJs`. -/
theorem table_ok {s : State} {B : BitVec 32} {Z W : Nat} (hw : Ws s B Z W nArr) (hW : 10 ≤ W) :
    WP isa (seqs table) s fun t => Ws t B Z W nArr ∧ Keep B W tabJs [] s.mem t.mem ∧
      (∀ j < nT W, w32 t.mem (State.addr B) (arr W aTab + 4 * j) = tabWord32 j) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hfit := hw.fits
  have hz : arr W aTab + 4 * nT W ≤ Z := by
    have := nT_le hW; simp only [arr, S, nArr, aTab] at *; omega
  simp only [table, seqs]
  rw [List.append_assoc, List.append_assoc]
  refine WP.seq (ptr_ok hw (r := .r12) (by decide) (by decide) fun s1 p1 r1 m1 hw1 => ?_)
  refine WP.append (tabSteps_ok hw1 (o := arr W aTab) (a := 0) p1 256 (by decide)
    (by have := nT_le hW; simp only [nT] at hz; split at hz <;> omega)) fun s2 ⟨e2, k2, O2⟩ => ?_
  have hw2 := hw1.rest k2
  -- `r1 := W ≥ 35`, and Z iff not.
  unfold bigW
  refine wp_subsC (op2_imm (by decide)) fun s3 u3 c3 => wp_movC (op2_imm (by decide)) fun s4 u4 c4 =>
    wp_adc (op2_imm (by decide)) fun s5 u5 => wp_cmp (op2_imm (by decide)) fun s6 f6 z6 => WP.block_nil ?_
  have k6 : Rest [.r1] s2 s6 := (u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans
    (f6.rest _)))
  have m6 : s6.mem = s2.mem := by rw [f6.mem, u5.mem, u4.mem, u3.mem]
  have hw6 := hw2.rest k6
  have r16 : (s5.gpr .r1).toNat = if 35 ≤ W then 1 else 0 := by
    rw [u5.gpr, u4.gpr, c4, c3, hw2.r9]
    have : W < 2 ^ 32 := by have := hw.wle; omega
    have e : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
    by_cases h : 35 ≤ W <;> simp [h, e]
  have z6' : s6.z = decide (W < 35) := by
    rw [z6]
    by_cases h : 35 ≤ W
    · have : s5.gpr .r1 = 1 := BitVec.eq_of_toNat_eq (by rw [r16]; simp [h])
      rw [this]; simp; omega
    · have : s5.gpr .r1 = 0 := BitVec.eq_of_toNat_eq (by rw [r16]; simp [h])
      rw [this]; simp; omega
  have O0 : Outside (State.addr B) (arr W aTab) (4 * 256) s.mem s6.mem := by rw [m6, ← m1]; simpa using O2
  have sp6 : s6.sp = s.sp ∧ s6.rd = s.rd ∧ s6.wr = s.wr :=
    ⟨by rw [k6.sp, k2.sp, r1.sp], by rw [k6.rd, k2.rd, r1.rd], by rw [k6.wr, k2.wr, r1.wr]⟩
  refine WP.ite (s6.z) rfl (fun hz6 => ?_) (fun hz6 => ?_)
  · -- `W < 35`: the first 256 words alone.
    have hW' : ¬ 35 ≤ W := by
      intro h; rw [z6'] at hz6; simp at hz6; omega
    refine WP.block_nil ⟨hw6, keep_span (a := aTab) (k := 27) O0 (Nat.le_refl _) ?_ fun j h1 h2 => tabJs_mem h1 h2,
      fun j hj => ?_, sp6⟩
    · have := nT_le hW; simp only [nT, hW', ↓reduceIte, arr, S, aTab] at *; omega
    · simp only [nT, hW', ↓reduceIte] at hj
      rw [m6]; simpa using e2 j hj
  · -- `W ≥ 35`: the other 256 words too.
    have hW' : 35 ≤ W := by
      rw [z6'] at hz6; simp at hz6; omega
    have hz' : arr W aTab + 4 * 512 ≤ Z := by simpa [nT, hW'] using hz
    have := hw.nowrap
    refine ptr_ok hw6 (r := .r12) (by decide) (by decide) (rest := tabWrite 256 256)
      fun s7 p7 r7 m7 hw7 => ?_
    rw [← List.append_nil (tabWrite 256 256)]
    refine WP.append (tabSteps_ok hw7 (o := arr W aTab) (a := 256) p7 256 (by decide)
      (by simp only [nT, hW', ↓reduceIte] at hz; omega)) fun s8 ⟨e8, k8, O8⟩ => WP.block_nil ?_
    have O1 : Outside (State.addr B) (arr W aTab) (4 * 512) s.mem s8.mem :=
      (O0.mono (Nat.le_refl _) (by omega)).trans (by rw [m7] at O8; exact O8.mono (by omega) (by omega))
    refine ⟨hw7.rest k8, keep_span (a := aTab) (k := 27) O1 (Nat.le_refl _) ?_ fun j h1 h2 => tabJs_mem h1 h2,
      fun j hj => ?_, ⟨by rw [k8.sp, r7.sp, sp6.1], by rw [k8.rd, r7.rd, sp6.2.1], by rw [k8.wr, r7.wr, sp6.2.2]⟩⟩
    · simp only [arr, S, aTab]; omega
    · simp only [nT, hW', ↓reduceIte] at hj
      rcases Nat.lt_or_ge j 256 with h | h
      · rw [O8.w32 (by omega) (by omega), m7, m6]; simpa using e2 j h
      · have := e8 (j - 256) (by omega)
        rwa [show 256 + (j - 256) = j by omega] at this

end VG.Proof.RsaKeyGen.Arm.Cand
