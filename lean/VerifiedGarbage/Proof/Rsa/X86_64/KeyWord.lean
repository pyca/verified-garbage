module
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFast
public import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard

import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.KeyParts
import VerifiedGarbage.Proof.Rsa.WordFactors
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_rsa_check_key` on x86-64: a word-level remainder in the checks' context

`WordDivide` (`vg_rsa_crt_values`'s normalized long division) works in the
same workspace as the checks, in arrays 3, 5, 8, 9 and 16, which leave `n`
and 1 alone (`KCtx.frm`), given the stride in the header (`WRoom`).
`wordRemK`: `d mod [aM]` compared with `[aX]`, and'ed into `sMask`; the
remainder is right when `[aM]` has exactly `w / 2` words, its top bit set.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

/-- The low `k` words of a number of `n ≥ k` words. -/
theorem wv_trunc (m : Mem) (p : Addr) (d : Nat) {k n : Nat} (hk : k ≤ n) :
    wv m p d k = wv m p d n % 2 ^ (64 * k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [wv_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wv_lt m p d k)]

/-- A number of `n ≥ k` words below `2^(64 k)` is its low `k` words. -/
theorem wv_of_lt (m : Mem) (p : Addr) (d : Nat) {k n : Nat} (hk : k ≤ n) (h : wv m p d n < 2 ^ (64 * k)) :
    wv m p d k = wv m p d n := by
  rw [wv_trunc m p d hk, Nat.mod_eq_of_lt h]

section
variable {s t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

/-- What `WordDivide` needs beyond the checks' context: the stride in the
header of the entry state, room for 17 arrays and `w` from 4. -/
structure WRoom (s : State) (B : Addr) (Z w : Nat) : Prop where
  hS : word s.mem B (8 * Impl.Rsa.X86_64.Keys.sStride) = BitVec.ofNat 64 (8 * (w + 2))
  hZ : slot w 17 ≤ Z
  w4 : 6 ≤ w
  w2 : w < 2 ^ 24

theorem KCtx.ws (h : KCtx s t B Z w minv N) (r : WRoom s B Z w) : Ws t B Z w :=
  ⟨h.good.scr, h.good.rdi, h.good.hdr.hw, by rw [h.hdr _ (by decide) (by decide)]; exact r.hS,
    h.good.hdr.harr, Nat.le_trans (by unfold slot; omega_arith) r.hZ, by have := r.w4; omega_arith, r.w2⟩

/-- A range of the arrays that leaves `n` (array 0) and 1 (array 7) alone. -/
def Away (w : Nat) (r : Nat × Nat) : Prop := (slot w 1 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 7) ∨ slot w 8 ≤ r.1

theorem away_slot (w : Nat) {j : Nat} (hj : 1 ≤ j) (hj' : j < 7 ∨ 8 ≤ j) {n : Nat} (hn : n ≤ 8 * (w + 2)) :
    Away w (slot w j, n) := by
  rcases hj' with hj' | hj'
  · refine .inl ⟨?_, ?_⟩ <;> dsimp only
    · unfold slot; have := Nat.mul_le_mul_right (8 * (w + 2)) hj; omega_arith
    · have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ 7 by omega_arith)
      rw [Nat.add_mul, Nat.one_mul] at this
      unfold slot; omega_arith
  · refine .inr ?_; dsimp only; unfold slot; have := Nat.mul_le_mul_right (8 * (w + 2)) hj'; omega_arith

theorem KCtx.frm (h : KCtx s t B Z w minv N) {rs : List (Nat × Nat)} (hf : Frm B rs t.mem t'.mem)
    (ha : ∀ r ∈ rs, Away w r) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ Z) (hk : Keep mmRegs t t') :
    KCtx s t' B Z w minv N := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have s01 : slot w 0 + 8 * (w + 2) = slot w 1 := by unfold slot; omega_arith
  have s78 : slot w 7 + 8 * (w + 2) = slot w 8 := by unfold slot; omega_arith
  have hh : ∀ i < 32, word t'.mem B (8 * i) = word t.mem B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => .inl (by
      have := hdr_lt_slot w 1 hi
      have := hdr_lt_slot w 8 hi
      rcases ha r hr with ⟨a, -⟩ | a <;> omega_arith)) (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine ⟨⟨h.good.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.good.rdi,
      ⟨(hh _ (by decide)).trans h.good.hdr.hw, (hh _ (by decide)).trans h.good.hdr.hminv,
        fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (h.good.hdr.harr j hj)⟩⟩,
    h.hZ, h.w1, h.w2, fun i hi hi' => (hh i hi).trans (h.hdr i hi hi'), h.ins.trans (InScr.of_frm hf hz),
    hk.2.1.trans h.rd, hk.2.2.trans h.wr, ?_, ?_, (h.keep.trans hk).mono (by decide)⟩
  · have e0 : slot w aN = slot w 0 := rfl
    have h0 : ∀ r ∈ rs, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN := by
      intro r hr
      refine .inl ?_
      rw [e0]
      have := slot_le (w := w) (show 0 < 8 by decide)
      rcases ha r hr with ⟨a, -⟩ | a <;> omega_arith
    rw [hf.wv_eq h0 (by have := slot_le (w := w) (show 0 < 8 by decide); rw [e0]; omega_arith)]
    exact h.n
  · have e7 : slot w aOne = slot w 7 := rfl
    have h7 : ∀ r ∈ rs, slot w aOne + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aOne := by
      intro r hr
      rcases ha r hr with ⟨-, a⟩ | a
      · exact .inr (by rw [e7]; exact a)
      · have := slot_le (w := w) (show 7 < 8 by decide)
        exact .inl (by rw [e7]; omega_arith)
    rw [hf.wv_eq h7 (by have := slot_le (w := w) (show 7 < 8 by decide); rw [e7]; omega_arith)]
    exact h.one

theorem KCtx.same (h : KCtx s t B Z w minv N) (hm : t'.mem = t.mem) (hk : Keep mmRegs t t') :
    KCtx s t' B Z w minv N :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) hk

theorem slot_eq (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := rfl

/-- Arrays 1 and 4 (`aX` and `aM`), which a frame of `WordDivide`'s ranges
leaves alone. -/
theorem wv_norm {m m' : Mem} (hf : Frm B (WordDivide.normRanges w) m m') (hn : B.toNat + Z ≤ 2 ^ 64)
    (hZ : slot w 17 ≤ Z) {j : Nat} (hj : j = 1 ∨ j = 4) :
    wv m' B (slot w j) w = wv m B (slot w j) w := by
  have h17 := slot_eq w 17
  refine hf.wv_eq (fun r hr => ?_) (by rcases hj with rfl | rfl <;> rw [slot_eq] <;> omega_arith)
  simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false,
    Impl.Rsa.X86_64.WordDivide.aM, Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aT,
    Impl.Rsa.X86_64.WordDivide.aV] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl <;> simp only [slot_eq] <;> omega_arith

theorem norm_away {w : Nat} (hw : 1 ≤ w) : ∀ r ∈ WordDivide.normRanges w, Away w r := fun r' hr' => by
  simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false,
    Impl.Rsa.X86_64.WordDivide.aM, Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aT,
    Impl.Rsa.X86_64.WordDivide.aV] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · exact away_slot w (j := 9) (by decide) (.inr (by decide)) (Nat.le_refl _)
  · exact away_slot w (j := 3) (by decide) (.inl (by decide)) (Nat.le_refl _)
  · refine away_slot w (j := 8) (by decide) (.inr (by decide)) ?_; omega_arith
  · refine away_slot w (j := 16) (by decide) (.inr (by decide)) ?_; omega_arith

theorem norm_bound {w Z : Nat} (hw : 1 ≤ w) (hZ : slot w 17 ≤ Z) : ∀ r ∈ WordDivide.normRanges w, r.1 + r.2 ≤ Z := fun r' hr' => by
  simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false,
    Impl.Rsa.X86_64.WordDivide.aM, Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aT,
    Impl.Rsa.X86_64.WordDivide.aV] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · have := slot_lt (w := w) (show 9 < 17 by decide); dsimp only; omega_arith
  · have := slot_lt (w := w) (show 3 < 17 by decide); dsimp only; omega_arith
  · have := slot_lt (w := w) (show 8 < 17 by decide); dsimp only; omega_arith
  · have := slot_lt (w := w) (show 16 < 17 by decide); dsimp only; omega_arith

/-- `andZero` keeps the checks' context, whatever the mask. -/
theorem andZeroK (h : KCtx s t B Z w minv N) :
    WP isa (.block Impl.Rsa.X86_64.Keys.CrtValues.andZero) t fun t' => KCtx s t' B Z w minv N := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have hmz : 8 * sMask + 8 < 2 ^ 64 := by unfold sMask sFn; omega_arith
  have hl := h.good.scr.ld (d := 8 * sMask) (by have := hdr_lt_slot w 8 (show sMask < 32 by decide); omega_arith)
  have hst := h.good.scr.st (d := 8 * sMask) (by have := hdr_lt_slot w 8 (show sMask < 32 by decide); omega_arith)
  refine WP.mono (WP.keep [.rbp] (Q := fun t' => ∃ v : BitVec 64, t'.mem = t.mem.writeW (off B (8 * sMask)) v) (by
    unfold Impl.Rsa.X86_64.Keys.CrtValues.andZero
    xrun [State.ea, hdr, h.good.rdi, hdrOff, hl, hst]
    exact ⟨_, rfl⟩) rfl) fun t' ⟨⟨v, hm⟩, k⟩ =>
    h.msk (by rw [hm]; exact writeW_outside _ B _ (Nat.le_of_lt hmz)) (k.mono (by decide))

/-- `d mod [aM]`, compared with `[aX]` and and'ed into `sMask`. -/
theorem wordRemK (h : KCtx s t B Z w minv N) (r : WRoom s B Z w) {b : Bool}
    (hm : word t.mem B (8 * sMask) = mask b) {pd : Addr} {db : List Byte} (hpd : word s.mem B (8 * sD) = pd)
    (hdl : word s.mem B (8 * sDlen) = BitVec.ofNat 64 db.length) (srcD : Src s B Z pd db)
    (hd1 : 1 ≤ db.length) (hdk : db.length ≤ 8 * w) :
    WP isa (seqs wordRem) t fun t' => KCtx s t' B Z w minv N ∧
      wv t'.mem B (slot w aX) w = wv t.mem B (slot w aX) w ∧ wv t'.mem B (slot w aM) w = wv t.mem B (slot w aM) w ∧
      ∃ Y : Nat, (2 ^ (64 * (w / 2) - 1) ≤ wv t.mem B (slot w aM) w →
          wv t.mem B (slot w aM) w < 2 ^ (64 * (w / 2)) → Y = Spec.Rsa.os2ip db % wv t.mem B (slot w aM) w) ∧
        word t'.mem B (8 * sMask) = mask (b && decide (Y = wv t.mem B (slot w aX) w)) := by
  have hn := h.good.scr.nowrap
  have hZ := r.hZ
  have w4 := r.w4
  have w2 := r.w2
  have sl : ∀ j < 17, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt hj) hZ
  have hm0 : ∀ m : Mem, ∀ j, 8 * sMask + 8 ≤ slot w j := fun _ j => hdr_lt_slot w j (by decide)
  have hmz : 8 * sMask + 8 < 2 ^ 64 := by unfold sMask sFn; omega_arith
  unfold wordRem
  simp only [List.append_assoc]
  -- `[9] := [aM]`
  refine wsa (by simp) (by simp) (WP.mono (copyA_ok (h.ws r)
    (o := Impl.Rsa.X86_64.WordDivide.aM) (a := aM) (by decide) (by decide) (by decide)) fun t₁ ⟨v₁, o₁, k₁⟩ => ?_)
  have f₁ : Frm B [(slot w 9, 8 * w)] t.mem t₁.mem := Frm.of_outside o₁ (List.mem_singleton_self _)
  have h₁ := h.frm f₁ (by simp only [List.mem_singleton, forall_eq]; exact away_slot w (by decide) (.inr (by decide)) (by omega_arith))
    (by simp only [List.mem_singleton, forall_eq]; have := sl 9 (by decide); omega_arith) (k₁.mono (by decide))
  have e₁ : ∀ j, j = 1 ∨ j = 4 → wv t₁.mem B (slot w j) w = wv t.mem B (slot w j) w := fun j hj =>
    o₁.wv (.inl (by rcases hj with rfl | rfl <;> simp only [slot_eq, Impl.Rsa.X86_64.WordDivide.aM] <;> omega_arith))
      (by have := hZ; rcases hj with rfl | rfl <;> simp only [slot_eq] at * <;> omega_arith)
  -- `[5] := d`
  refine wsa (by simp [loadNum]) (by simp) (WP.mono (loadK h₁ (j := aT) (by decide) (by decide) (by decide)
    (show sD < 32 by decide) (show sDlen < 32 by decide) (by decide) (by decide) hpd hdl srcD hd1 hdk)
    fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  have o₂ : Outside B (slot w 5) (8 * (w + 2)) t₁.mem t₂.mem := fun x hx => a₂ x (by
    simp only [List.mem_singleton, forall_eq]; exact hx)
  have e₂ : ∀ j, j = 1 ∨ j = 4 ∨ j = 9 → wv t₂.mem B (slot w j) w = wv t₁.mem B (slot w j) w := fun j hj => by
    have := hZ
    refine o₂.wv ?_ (by rcases hj with rfl | rfl | rfl <;> simp only [slot_eq] at * <;> omega_arith)
    rcases hj with rfl | rfl | rfl
    · exact .inl (by simp only [slot_eq]; omega_arith)
    · exact .inl (by simp only [slot_eq]; omega_arith)
    · exact .inr (by simp only [slot_eq]; omega_arith)
  -- the division
  refine wsa (by simp) (by simp [Impl.Rsa.X86_64.Keys.eqA]) (WP.mono (WordDivide.fast_ok (h₂.ws r) hZ w4)
    fun t₃ ⟨v₃, f₃, k₃⟩ => ?_)
  have h₃ := h₂.frm f₃ (fun r' hr' => by
      simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false,
        Impl.Rsa.X86_64.WordDivide.aM, Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aT,
        Impl.Rsa.X86_64.WordDivide.aV] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      · exact away_slot w (by decide) (.inr (by decide)) (Nat.le_refl _)
      · exact away_slot w (by decide) (.inl (by decide)) (Nat.le_refl _)
      · exact away_slot w (by decide) (.inr (by decide)) (by omega_arith)
      · exact away_slot w (by decide) (.inr (by decide)) (by omega_arith))
    (fun r' hr' => by
      simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false,
        Impl.Rsa.X86_64.WordDivide.aM, Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aT,
        Impl.Rsa.X86_64.WordDivide.aV] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      · exact sl 9 (by decide)
      · exact sl 3 (by decide)
      · have := sl 8 (by decide); dsimp only; omega_arith
      · have := sl 16 (by decide); dsimp only; omega_arith) k₃
  -- the comparison
  refine wsa (by simp [Impl.Rsa.X86_64.Keys.eqA]) (by simp) (WP.mono (eqA_ok (h₃.ws r)
    (a := Impl.Rsa.X86_64.WordDivide.aR) (b := aX) (by decide) (by decide)) fun t₄ ⟨z₄, m₄, k₄⟩ => ?_)
  have h₄ := h₃.same m₄ (k₄.mono (by decide))
  have mk₃ : word t₃.mem B (8 * sMask) = mask b := by
    rw [f₃.word_eq (fun r' hr' => by
        simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl <;> exact .inl (hm0 t.mem _)) (Nat.le_of_lt hmz),
      o₂.word (.inl (hm0 t.mem _)) (Nat.le_of_lt hmz),
      o₁.word (.inl (hm0 t.mem _)) (Nat.le_of_lt hmz), hm]
  refine WP.mono (andZero_ok (h₄.ws r) (c := b) (by rw [m₄]; exact mk₃) z₄) fun t₅ ⟨m₅, k₅⟩ => ?_
  have h₅ := h₄.msk (by rw [m₅]; exact writeW_outside _ B _ (Nat.le_of_lt hmz)) (k₅.mono (by decide))
  have e₅ : ∀ j, j = 1 ∨ j = 4 → wv t₅.mem B (slot w j) w = wv t.mem B (slot w j) w := fun j hj => by
    rw [m₅, (writeW_outside _ B _ (Nat.le_of_lt hmz)).wv (.inr (by have := hm0 t.mem j; omega_arith))
      (by have := hZ; rcases hj with rfl | rfl <;> simp only [slot_eq] at * <;> omega_arith), m₄,
      wv_norm f₃ hn hZ hj, e₂ j (by omega_arith), e₁ j hj]
  refine ⟨h₅, e₅ aX (.inl rfl), e₅ aM (.inr rfl), wv t₃.mem B (slot w 3) w, fun hb hlt => ?_, ?_⟩
  · -- the divisor is `[aM]`, normalized already
    have d₂ : wv t₂.mem B (slot w 9) (w / 2) = wv t.mem B (slot w aM) w := by
      simp only [Impl.Rsa.X86_64.WordDivide.aM] at v₁
      rw [wv_trunc _ _ _ (show w / 2 ≤ w by omega_arith), e₂ 9 (by decide), v₁,
        Nat.mod_eq_of_lt hlt]
    have top := WordDivide.top_of_bound (m := t₂.mem) (B := B) (e := slot w 9) (show 1 ≤ w / 2 by omega_arith)
      (by rw [d₂]; exact hb)
    have q := v₃ top
    simp only [Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aD, Impl.Rsa.X86_64.WordDivide.aM] at q
    rw [show slot w 5 = slot w aT from rfl, v₂, d₂] at q
    have pos : 0 < wv t.mem B (slot w aM) w := by have := Nat.one_le_two_pow (n := 64 * (w / 2) - 1); omega_arith
    have lt : Spec.Rsa.os2ip db % wv t.mem B (slot w aM) w < 2 ^ (64 * w) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ pos)
        (Nat.le_trans (Nat.le_of_lt hlt) (Nat.pow_le_pow_right (by decide) (by omega_arith)))
    rw [wv_of_lt _ _ _ (Nat.le_succ w) (by rw [q]; exact lt), q]
  · have ex : wv t₃.mem B (slot w aX) w = wv t.mem B (slot w aX) w := by
      rw [wv_norm f₃ hn hZ (j := aX) (.inl rfl), e₂ aX (by decide), e₁ aX (.inl rfl)]
    rw [m₅, word_writeW_self, ex]; rfl

/-- `remOne top`: `[aAcc] mod [aM]` (the accumulator's low `w` words, of the words `top` gives)
compared with 1 and and'ed into `sMask`, the remainder right when `[aM]` has `w / 2` words, its top
bit set. -/
theorem remOneK (h : KCtx s t B Z w minv N) (r : WRoom s B Z w) {b : Bool}
    (hm : word t.mem B (8 * sMask) = mask b) {top : Option Nat} (hk : ∀ k, top = some k → k ≤ w / 2)
    (hX : wv t.mem B (slot w aAcc) w < 2 ^ (64 * WordDivide.xw w top)) :
    WP isa (seqs (remOne top)) t fun t' => KCtx s t' B Z w minv N ∧ ∃ R : Nat,
      (2 ^ (64 * (w / 2) - 1) ≤ wv t.mem B (slot w aM) w → wv t.mem B (slot w aM) w < 2 ^ (64 * (w / 2)) →
        R = wv t.mem B (slot w aAcc) w % wv t.mem B (slot w aM) w) ∧
      word t'.mem B (8 * sMask) = mask (b && decide (R = 1)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have hZ17 := r.hZ
  have w4 := r.w4
  have := h.w2
  have hm0 : ∀ j, 8 * sMask + 8 ≤ slot w j := fun j => hdr_lt_slot w j (by decide)
  have hmz : 8 * sMask + 8 < 2 ^ 64 := by unfold sMask sFn; omega_arith
  simp only [remOne, List.append_assoc]
  -- `[5] := ` the accumulator's low `w` words
  refine wsa (by simp) (by simp) (WP.mono (copyA_ok (h.ws r)
    (o := Impl.Rsa.X86_64.WordDivide.aD) (a := aAcc) (by decide) (by decide) (by decide)) fun t₆ ⟨v₆, o₆, k₆⟩ => ?_)
  simp only [Impl.Rsa.X86_64.WordDivide.aD] at v₆ o₆
  have h₆ := h.frm (Frm.of_outside o₆ (List.mem_singleton_self _))
    (by simp only [List.mem_singleton, forall_eq]; exact away_slot w (by decide) (.inl (by decide)) (by omega_arith))
    (by simp only [List.mem_singleton, forall_eq]; have := slot_lt (w := w) (show 5 < 17 by decide); omega_arith)
    (k₆.mono (by decide))
  have P₆ : wv t₆.mem B (slot w aM) w = wv t.mem B (slot w aM) w :=
    o₆.wv (.inl (by simp only [slot_eq, aM]; omega_arith)) (by have := slot_le (w := w) (show aM < 8 by decide); omega_arith)
  -- `[9] := [aM]`
  refine wsa (by simp) (by simp) (WP.mono (copyA_ok (h₆.ws r)
    (o := Impl.Rsa.X86_64.WordDivide.aM) (a := aM) (by decide) (by decide) (by decide)) fun t₇ ⟨v₇, o₇, k₇⟩ => ?_)
  simp only [Impl.Rsa.X86_64.WordDivide.aM] at v₇ o₇
  have h₇ := h₆.frm (Frm.of_outside o₇ (List.mem_singleton_self _))
    (by simp only [List.mem_singleton, forall_eq]; exact away_slot w (by decide) (.inr (by decide)) (by omega_arith))
    (by simp only [List.mem_singleton, forall_eq]; have := slot_lt (w := w) (show 9 < 17 by decide); omega_arith)
    (k₇.mono (by decide))
  have D₇ : wv t₇.mem B (slot w 5) w = wv t₆.mem B (slot w 5) w :=
    o₇.wv (.inl (by simp only [slot_eq]; omega_arith)) (by have := slot_lt (w := w) (show 5 < 17 by decide); omega_arith)
  -- the division
  refine wsa (by simp) (by simp [Impl.Rsa.X86_64.Keys.eqA]) (WP.mono (WordDivide.fastAt_ok (h₇.ws r) hZ17 w4 hk)
    fun t₈ ⟨v₈, f₈, k₈⟩ => ?_)
  have h₈ := h₇.frm f₈ (fun r' hr' => by
      simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false,
        Impl.Rsa.X86_64.WordDivide.aM, Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aT,
        Impl.Rsa.X86_64.WordDivide.aV] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      · exact away_slot w (by decide) (.inr (by decide)) (Nat.le_refl _)
      · exact away_slot w (by decide) (.inl (by decide)) (Nat.le_refl _)
      · exact away_slot w (by decide) (.inr (by decide)) (by omega_arith)
      · exact away_slot w (by decide) (.inr (by decide)) (by omega_arith))
    (fun r' hr' => by
      simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false,
        Impl.Rsa.X86_64.WordDivide.aM, Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aT,
        Impl.Rsa.X86_64.WordDivide.aV] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      · have := slot_lt (w := w) (show 9 < 17 by decide); dsimp only; omega_arith
      · have := slot_lt (w := w) (show 3 < 17 by decide); dsimp only; omega_arith
      · have := slot_lt (w := w) (show 8 < 17 by decide); dsimp only; omega_arith
      · have := slot_lt (w := w) (show 16 < 17 by decide); dsimp only; omega_arith) k₈
  -- the comparison with 1
  refine wsa (by simp [Impl.Rsa.X86_64.Keys.eqA]) (by simp) (WP.mono (eqA_ok (h₈.ws r)
    (a := Impl.Rsa.X86_64.WordDivide.aR) (b := aOne) (by decide) (by decide)) fun t₉ ⟨z₉, m₉, k₉⟩ => ?_)
  have h₉ := h₈.same m₉ (k₉.mono (by decide))
  have mk₈ : word t₈.mem B (8 * sMask) = mask b := by
    rw [f₈.word_eq (fun r' hr' => by
        simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl <;> exact .inl (hm0 _)) (Nat.le_of_lt hmz),
      o₇.word (.inl (hm0 _)) (Nat.le_of_lt hmz), o₆.word (.inl (hm0 _)) (Nat.le_of_lt hmz), hm]
  rw [h₈.one] at z₉
  refine WP.mono (andZero_ok (h₉.ws r) (c := b) (by rw [m₉]; exact mk₈) z₉) fun t₁₀ ⟨m₁₀, k₁₀⟩ => ?_
  have h₁₀ := h₉.msk (by rw [m₁₀]; exact writeW_outside _ B _ (Nat.le_of_lt hmz)) (k₁₀.mono (by decide))
  refine ⟨h₁₀, wv t₈.mem B (slot w 3) w, fun hb hlt => ?_, by rw [m₁₀, word_writeW_self]; rfl⟩
  have d₇ : wv t₇.mem B (slot w 9) (w / 2) = wv t.mem B (slot w aM) w := by
    rw [wv_trunc _ _ _ (show w / 2 ≤ w by omega_arith), v₇, P₆, Nat.mod_eq_of_lt hlt]
  have htop := WordDivide.top_of_bound (m := t₇.mem) (B := B) (e := slot w 9) (show 1 ≤ w / 2 by omega_arith)
    (by rw [d₇]; exact hb)
  have q := v₈ (by simp only [Impl.Rsa.X86_64.WordDivide.aD]; rw [D₇, v₆]; exact hX) htop
  simp only [Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aD, Impl.Rsa.X86_64.WordDivide.aM] at q
  rw [D₇, v₆, d₇] at q
  have pos : 0 < wv t.mem B (slot w aM) w := by have := Nat.one_le_two_pow (n := 64 * (w / 2) - 1); omega_arith
  have lt : wv t.mem B (slot w aAcc) w % wv t.mem B (slot w aM) w < 2 ^ (64 * w) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ pos)
      (Nat.le_trans (Nat.le_of_lt hlt) (Nat.pow_le_pow_right (by decide) (by omega_arith)))
  rw [wv_of_lt _ _ _ (Nat.le_succ w) (by rw [q]; exact lt), q]

/-- `wordMod`: `dX < M`, `d mod M = dX` (when `M = X - 1` has `w / 2`
words, its top bit set) and `e dX mod M = 1`, for `M = X - 1`. -/
theorem wordModK (h : KCtx s t B Z w minv N) (r : WRoom s B Z w) {b : Bool}
    (hm : word t.mem B (8 * sMask) = mask b)
    {sX sXlen sDX : Nat} (hsX : sX < 32) (hsXl : sXlen < 32) (hsDX : sDX < 32)
    (nX : sX ≠ sMask) (nXl : sXlen ≠ sMask) (nDX : sDX ≠ sMask)
    {px pdx pd : Addr} {xb dxb db : List Byte}
    (hpx : word s.mem B (8 * sX) = px) (hxl : word s.mem B (8 * sXlen) = BitVec.ofNat 64 xb.length)
    (hpdx : word s.mem B (8 * sDX) = pdx) (hpd : word s.mem B (8 * sD) = pd)
    (hdl : word s.mem B (8 * sDlen) = BitVec.ofNat 64 db.length)
    (srcX : Src s B Z px xb) (srcDX : Src s B Z pdx dxb) (srcD : Src s B Z pd db)
    (hdxl : dxb.length = xb.length) (hx1 : 1 ≤ xb.length) (hxk : xb.length ≤ 8 * (w / 2))
    (hd1 : 1 ≤ db.length) (hdk : db.length ≤ 8 * w)
    (hev : (word s.mem B (8 * sEv)).toNat < 2 ^ 33) :
    WP isa (seqs (wordMod sX sXlen sDX)) t fun t' => KCtx s t' B Z w minv N ∧
      ∃ M Y R2 : Nat, (0 < Spec.Rsa.os2ip xb → M = Spec.Rsa.os2ip xb - 1) ∧
        (2 ^ (64 * (w / 2) - 1) ≤ M → M < 2 ^ (64 * (w / 2)) → Y = Spec.Rsa.os2ip db % M) ∧
        (0 < Spec.Rsa.os2ip xb → 2 ^ (64 * (w / 2) - 1) ≤ M → M < 2 ^ (64 * (w / 2)) → Spec.Rsa.os2ip dxb < M →
          R2 = (word s.mem B (8 * sEv)).toNat * Spec.Rsa.os2ip dxb % M) ∧
        word t'.mem B (8 * sMask) =
          mask (b && decide (Spec.Rsa.os2ip dxb < M) && decide (Y = Spec.Rsa.os2ip dxb) && decide (R2 = 1)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have := h.w2
  simp only [wordMod, List.append_assoc]
  refine wsa (by simp [loadNum]) (by simp [decM]) (WP.mono (loadK h (j := aM) (by decide) (by decide)
    (by decide) hsX hsXl nX nXl hpx hxl srcX hx1 (by omega_arith)) fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine wsa (by simp [decM]) (by simp [loadNum]) (WP.mono (decK h₁) fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  rw [v₁] at v₂
  refine wsa (by simp [loadNum]) (by simp [ltMask]) (WP.mono (loadK h₂ (j := aX) (by decide) (by decide)
    (by decide) hsDX hsXl nDX nXl hpdx (by rw [hdxl]; exact hxl) srcDX (by omega_arith) (by omega_arith))
    fun t₃ ⟨h₃, v₃, a₃⟩ => ?_)
  have M₃ : wv t₃.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := Arrays.wv_other a₃ (by decide) (by decide) hZ hn
  refine wsa (by simp [ltMask]) (by simp [wordRem]) (WP.mono (ltK h₃ (a := aX) (b := aM) (by decide) (by decide))
    fun t₄ ⟨h₄, m₄, o₄⟩ => ?_)
  rw [v₃, M₃, Arrays.mask_eq a₃ hn hZ, Arrays.mask_eq a₂ hn hZ, Arrays.mask_eq a₁ hn hZ, hm, mask_and'] at m₄
  have M₄ : wv t₄.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Outside.wv_arr o₄ (by decide) hZ hn (by omega_arith), M₃]
  have X₄ : wv t₄.mem B (slot w aX) w = Spec.Rsa.os2ip dxb := by
    rw [Outside.wv_arr o₄ (by decide) hZ hn (by omega_arith), v₃]
  refine wsa (by simp [wordRem]) (by simp [mulE]) (WP.mono (wordRemK h₄ r m₄ hpd hdl srcD hd1 hdk)
    fun t₅ ⟨h₅, X₅, M₅, Y, hY, m₅⟩ => ?_)
  rw [M₄] at hY M₅
  rw [X₄] at X₅ m₅
  refine wsa (by simp [mulE]) (by simp [remOne]) (WP.mono (mulEK h₅) fun t₁₀ ⟨h₁₀, v₁₀, a₁₀⟩ => ?_)
  have M₁₀ : wv t₁₀.mem B (slot w aM) w = wv t₂.mem B (slot w aM) w := by
    rw [Arrays.wv_other a₁₀ (by decide) (by decide) hZ hn, M₅]
  rw [X₅] at v₁₀
  -- the product's `w / 2 + 1` words
  have hdx : Spec.Rsa.os2ip dxb < 2 ^ (64 * (w / 2)) :=
    Nat.lt_of_lt_of_le (os2ip_lt dxb) (by
      rw [hdxl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega_arith))
  have prod : (word s.mem B (8 * sEv)).toNat * Spec.Rsa.os2ip dxb < 2 ^ (64 * (w / 2 + 1)) := by
    rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm (2 ^ (64 * (w / 2)))]
    exact Nat.mul_lt_mul'' (by omega_arith) hdx
  have accw : wv t₁₀.mem B (slot w aAcc) w = (word s.mem B (8 * sEv)).toNat * Spec.Rsa.os2ip dxb := by
    rw [wv_of_lt _ _ _ (show w ≤ w + 2 by omega_arith) (by
      rw [v₁₀]; exact Nat.lt_of_lt_of_le prod (Nat.pow_le_pow_right (by decide) (by omega_arith))), v₁₀]
  have mk₁₀ : word t₁₀.mem B (8 * sMask) = mask (b && decide (Spec.Rsa.os2ip dxb < wv t₂.mem B (slot w aM) w) &&
      decide (Y = Spec.Rsa.os2ip dxb)) := by
    rw [Arrays.mask_eq a₁₀ hn hZ, m₅]
  refine WP.mono (remOneK h₁₀ r mk₁₀ (top := some 1) (fun k e => by obtain rfl := Option.some.inj e; omega_arith)
    (by rw [accw]; exact prod)) fun t₁₂ ⟨h₁₂, R2, eR2, m₁₂⟩ => ⟨h₁₂, wv t₂.mem B (slot w aM) w, Y, R2,
    fun hx => by have := v₂ hx; omega_arith, hY, fun _ hb hlt _ => ?_, m₁₂⟩
  rw [M₁₀] at eR2
  rw [eR2 hb hlt, accw]

/-- `wordQInv`: `qInv < p` and `q qInv mod p = 1`, the remainder right when
`p` has `w / 2` words, its top bit set, and `q` fits in `w / 2` words. -/
theorem wordQInvK (h : KCtx s t B Z w minv N) (r : WRoom s B Z w) {b : Bool}
    (hm : word t.mem B (8 * sMask) = mask b)
    {pp pq pqi : Addr} {pb qb qib : List Byte} (hpp : word s.mem B (8 * sP) = pp)
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pb.length) (hpq : word s.mem B (8 * sQ) = pq)
    (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 qb.length) (hpqi : word s.mem B (8 * sQI) = pqi)
    (srP : Src s B Z pp pb) (srQ : Src s B Z pq qb) (srQI : Src s B Z pqi qib) (hqil : qib.length = pb.length)
    (hp1 : 1 ≤ pb.length) (hpk : pb.length ≤ 8 * w) (hq1 : 1 ≤ qb.length) (hqk : qb.length ≤ 8 * w) :
    WP isa (seqs wordQInv) t fun t' =>
      KCtx s t' B Z w minv N ∧ ∃ R : Nat,
        (2 ^ (64 * (w / 2) - 1) ≤ Spec.Rsa.os2ip pb → Spec.Rsa.os2ip pb < 2 ^ (64 * (w / 2)) →
          Spec.Rsa.os2ip qb < 2 ^ (64 * (w / 2)) → Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb →
          R = Spec.Rsa.os2ip qib * Spec.Rsa.os2ip qb % Spec.Rsa.os2ip pb) ∧
        word t'.mem B (8 * sMask) =
          mask (b && decide (Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) && decide (R = 1)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have := h.w2
  simp only [wordQInv, List.append_assoc]
  refine wsa (by simp [loadNum]) (by simp [loadNum]) (WP.mono (loadK h (j := aM) (by decide) (by decide)
    (by decide) (show sP < 32 by decide) (show sPlen < 32 by decide) (by decide) (by decide) hpp hpl srP hp1 hpk)
    fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine wsa (by simp [loadNum]) (by simp [ltMask]) (WP.mono (loadK h₁ (j := aX) (by decide) (by decide)
    (by decide) (show sQI < 32 by decide) (show sPlen < 32 by decide) (by decide) (by decide) hpqi
    (by rw [hqil]; exact hpl) srQI (by omega_arith) (by omega_arith)) fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  rw [← Arrays.wv_other a₂ (by decide) (by decide) hZ hn] at v₁
  refine wsa (by simp [ltMask]) (by simp [loadNum]) (WP.mono (ltK h₂ (a := aX) (b := aM) (by decide) (by decide))
    fun t₃ ⟨h₃, m₃, o₃⟩ => ?_)
  rw [v₁, v₂, Arrays.mask_eq a₂ hn hZ, Arrays.mask_eq a₁ hn hZ, hm, mask_and'] at m₃
  rw [← Outside.wv_arr o₃ (by decide) hZ hn (by omega_arith)] at v₁ v₂
  refine wsa (by simp [loadNum]) (by simp [mulPQ]) (WP.mono (loadK h₃ (j := aR) (by decide) (by decide)
    (by decide) (show sQ < 32 by decide) (show sQlen < 32 by decide) (by decide) (by decide) hpq hql srQ hq1 hqk)
    fun t₄ ⟨h₄, v₄, a₄⟩ => ?_)
  rw [← Arrays.wv_other a₄ (by decide) (by decide) hZ hn] at v₁ v₂
  -- `qInv` and `q` are their low `⌈len / 8⌉` words.
  have low : ∀ {bs : List Byte} {j L : Nat}, wv t₄.mem B (slot w j) w = Spec.Rsa.os2ip bs → bs.length = L →
      L ≤ 8 * w → wv t₄.mem B (slot w j) ((L + 7) / 8) = Spec.Rsa.os2ip bs := fun {bs j L} v hL hk => by
    rw [wv_low_of_lt (v := (L + 7) / 8) (w := w) (by omega) (by
      rw [v]; exact Nat.lt_of_lt_of_le (os2ip_lt bs) (by
        rw [hL, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega))), v]
  refine wsa (by simp [mulPQ]) (by simp [remOne]) (WP.mono (mulPQK h₄ hpl hql hp1 hq1 hpk hqk)
    fun t₅ ⟨h₅, v₅, a₅⟩ => ?_)
  rw [← Arrays.wv_other a₅ (by decide) (by decide) hZ hn] at v₁
  rw [low v₂ hqil hpk, low v₄ rfl hqk] at v₅
  have mk₅ : word t₅.mem B (8 * sMask) = mask (b && decide (Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb)) := by
    rw [Arrays.mask_eq a₅ hn hZ, Arrays.mask_eq a₄ hn hZ, m₃]
  refine WP.mono (remOneK h₅ r mk₅ (top := none) (fun _ e => nomatch e) (wv_lt _ _ _ _))
    fun t' ⟨h', R, eR, m'⟩ => ⟨h', R, fun hb hlt hq hqi => ?_, m'⟩
  have prod : Spec.Rsa.os2ip qib * Spec.Rsa.os2ip qb < 2 ^ (64 * w) := by
    have e : 2 ^ (64 * w) = 2 ^ (64 * (w / 2)) * 2 ^ (64 * (w / 2)) * 2 ^ (64 * (w % 2)) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_arith
    rw [e]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' (Nat.lt_trans hqi hlt) hq)
      (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have accw : wv t₅.mem B (slot w aAcc) w = Spec.Rsa.os2ip qib * Spec.Rsa.os2ip qb := by
    rw [wv_of_lt _ _ _ (show w ≤ 2 * w + 2 by omega_arith) (by rw [v₅]; exact prod), v₅]
  rw [← v₁] at hb hlt
  rw [eR hb hlt, accw, v₁]

/-- `guard`: `ZF` set iff the public shape is the one `WordDivide` serves. -/
theorem guardK (h : KCtx s t B Z w minv N) {k pl ql : Nat} {np : Addr} {nb : List Byte}
    (hk : word s.mem B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k)
    (hnp : word s.mem B (8 * Impl.Bignum.X86_64.Public.sN) = np)
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl) (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql)
    (srN : Src s B Z np nb) (hnl : 0 < nb.length) :
    WP isa (.block guard) t fun t' => KCtx s t' B Z w minv N ∧ t'.mem = t.mem ∧
      t'.zf = some (WordDivide.guardVal w k pl ql (nb[0]'hnl) == 0) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    h.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have sr := h.src srN
  refine WP.mono (WP.keep [.r12, .rdx, .rax, .rcx] (Q := fun t' => t'.mem = t.mem ∧
    t'.zf = some (WordDivide.guardVal w k pl ql (nb[0]'hnl) == 0)) (by
    xrun [Impl.Rsa.X86_64.CheckKey.guard, guardHead, guardTail, List.cons_append, List.nil_append, State.ea, hdr, h.good.rdi, hdrOff, hl sW (by decide), hl Impl.Bignum.X86_64.Public.sN (by decide),
      hl Impl.Bignum.X86_64.Public.sK (by decide), hl sPlen (by decide), hl sQlen (by decide), h.good.hdr.hw,
      h.hdr _ (show Impl.Bignum.X86_64.Public.sN < 32 by decide) (by decide), hnp,
      h.hdr _ (show Impl.Bignum.X86_64.Public.sK < 32 by decide) (by decide), hk,
      h.hdr _ (show sPlen < 32 by decide) (by decide), hpl, h.hdr _ (show sQlen < 32 by decide) (by decide), hql,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      show InRegions (t.rd ++ t.wr) np 1 by simpa using sr.rd 0 hnl,
      show t.mem np = nb[0] from by simpa using sr.val 0 hnl,
      WordDivide.guardVal]
    rfl) rfl) fun t' ⟨⟨hm, hz⟩, k'⟩ => ⟨h.same hm (k'.mono (by decide)), hm, hz⟩

end

/-! ## `keyValid` from the word-level checks -/

/-- With `x < m` and `e x ≡ 1`, `e d ≡ 1` iff `d mod m = x`. -/
theorem mod_swap {m e d x : Nat} (hx : x < m) (hex : e * x % m = 1) : e * d % m = 1 ↔ d % m = x := by
  constructor
  · intro hed
    calc d % m = d * (e * x) % m := by rw [Nat.mul_mod, hex, Nat.mul_one, Nat.mod_mod]
      _ = x * (e * d) % m := by rw [show d * (e * x) = x * (e * d) by ac_rfl]
      _ = x := by rw [Nat.mul_mod, hed, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hx]
  · intro hd
    rw [Nat.mul_mod, Nat.mod_eq_of_lt hx] at hex
    rw [Nat.mul_mod, hd, hex]

theorem part_iff {M x R Y e d : Nat} {T : Prop} (hR : x < M → R = e * x % M) (hY : Y = d % M) :
    (x < M ∧ e * d % M = 1 ∧ R = 1 ∧ T) ↔ (x < M ∧ Y = x ∧ R = 1 ∧ T) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by rw [hY]; exact (mod_swap h1 (by rw [← hR h1]; exact h3)).1 h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (mod_swap h1 (by rw [← hR h1]; exact h3)).2 (by rw [← hY]; exact h2), h3, h4⟩

/-- `keyValid` as the word-level checks compute it, for factors of `b`
bits each with the top bit set (which a balanced `n` gives, `hbal`). -/
theorem keyValid_word {k n e d p q dP dQ qInv b : Nat} (hm : Spec.Rsa.modulusValid n k = true)
    (he : Spec.Rsa.exponentValid e = true) (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1))
    {Mp Mq Yp Yq Rp2 Rq2 R : Nat} (hMp : 0 < p → Mp = p - 1) (hMq : 0 < q → Mq = q - 1)
    (hbal : p * q = n → (2 ^ (b - 1) ≤ p - 1 ∧ p < 2 ^ b) ∧ (2 ^ (b - 1) ≤ q - 1 ∧ q < 2 ^ b))
    (hYp : 2 ^ (b - 1) ≤ Mp → Mp < 2 ^ b → Yp = d % Mp)
    (hYq : 2 ^ (b - 1) ≤ Mq → Mq < 2 ^ b → Yq = d % Mq)
    (hR2 : 0 < p → 2 ^ (b - 1) ≤ Mp → Mp < 2 ^ b → dP < Mp → Rp2 = e * dP % Mp)
    (hR4 : 0 < q → 2 ^ (b - 1) ≤ Mq → Mq < 2 ^ b → dQ < Mq → Rq2 = e * dQ % Mq)
    (hR : 2 ^ (b - 1) ≤ p → p < 2 ^ b → q < 2 ^ b → qInv < p → R = qInv * q % p) :
    Spec.Rsa.keyValid k n e d p q dP dQ qInv = (true && decide (d < n) && decide (p * q = n) &&
      decide (dP < Mp) && decide (Yp = dP) && decide (Rp2 = 1) &&
      decide (dQ < Mq) && decide (Yq = dQ) && decide (Rq2 = 1) &&
      decide (qInv < p) && decide (R = 1)) := by
  -- `Rp2` and `Rq2` where the divisors have `b` bits, else the remainders themselves: the same
  -- where `p q = n`, the only case they decide.
  let Rp2' := if 2 ^ (b - 1) ≤ Mp ∧ Mp < 2 ^ b then Rp2 else e * dP % Mp
  let Rq2' := if 2 ^ (b - 1) ≤ Mq ∧ Mq < 2 ^ b then Rq2 else e * dQ % Mq
  have hR2' : 0 < p → dP < Mp → Rp2' = e * dP % Mp := fun h0 hlt => by
    simp only [Rp2']; split
    · next hb => exact hR2 h0 hb.1 hb.2 hlt
    · rfl
  have hR4' : 0 < q → dQ < Mq → Rq2' = e * dQ % Mq := fun h0 hlt => by
    simp only [Rq2']; split
    · next hb => exact hR4 h0 hb.1 hb.2 hlt
    · rfl
  rw [Proof.Rsa.keyValid_bounded_parts hm he hp hq (Rp1 := e * d % Mp) (Rq1 := e * d % Mq)
    (Rpq := qInv * q % p) hMp hMq (fun _ _ _ => rfl) hR2' (fun _ _ _ => rfl) hR4' (fun _ _ => rfl)]
  unfold Proof.Rsa.keyBits
  by_cases hd : d < n
  · by_cases hpq : p * q = n
    · obtain ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ := hbal hpq
      have pos := Nat.one_le_two_pow (n := b - 1)
      have eMp := hMp (by omega_arith)
      have eMq := hMq (by omega_arith)
      have ep : Rp2' = Rp2 := ite_eq_left ⟨by omega_arith, by omega_arith⟩
      have eq : Rq2' = Rq2 := ite_eq_left ⟨by omega_arith, by omega_arith⟩
      rw [ep, eq]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, true_and]
      rw [part_iff (fun h => hR2 (by omega_arith) (by omega_arith) (by omega_arith) h)
          (hYp (by omega_arith) (by omega_arith)),
        part_iff (T := qInv < p ∧ qInv * q % p = 1) (fun h => hR4 (by omega_arith) (by omega_arith) (by omega_arith) h)
          (hYq (by omega_arith) (by omega_arith))]
      constructor
      · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
        exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, by rw [hR (by omega_arith) p2 q2 a9]; exact a10⟩
      · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
        exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, by rw [← hR (by omega_arith) p2 q2 a9]; exact a10⟩
    · simp only [hpq, decide_false, Bool.and_false, Bool.false_and]
  · simp only [hd, decide_false, Bool.and_false, Bool.false_and]

/-- Under the guard, factors of `n` have `w / 2` words each, the top bit
set (`WordDivide.factors_word` for the checks' inputs). -/
theorem factors_guard {w k : Nat} {nb pb qb : List Byte} (hnl : nb.length = k) (hk1 : 1 ≤ k) (hk : k ≤ 1024)
    (hw : w = (k + 7) / 8) (hpl : pb.length < k) (hql : qb.length < k)
    (hg : WordDivide.guardVal w k pb.length qb.length (nb[0]'(by omega_arith)) = 0)
    (he : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb) :
    (2 ^ (64 * (w / 2) - 1) ≤ Spec.Rsa.os2ip pb - 1 ∧ Spec.Rsa.os2ip pb < 2 ^ (64 * (w / 2))) ∧
    (2 ^ (64 * (w / 2) - 1) ≤ Spec.Rsa.os2ip qb - 1 ∧ Spec.Rsa.os2ip qb < 2 ^ (64 * (w / 2))) := by
  have hw' : w < 2 ^ 24 := by omega_arith
  obtain ⟨hw2, hwk, hpk, hpq, hb⟩ := WordDivide.guard_zero hw' (by omega_arith) (by omega_arith)
    (by omega_arith) hg
  have hbits : 64 * (w / 2) = 32 * w := by omega_arith
  have ep : 8 * pb.length = 64 * (w / 2) := by omega_arith
  have eq : 8 * qb.length = 64 * (w / 2) := by omega_arith
  have pbound := Proof.Bignum.os2ip_lt pb
  have qbound := Proof.Bignum.os2ip_lt qb
  rw [Proof.Bignum.pow256_eq, ep] at pbound
  rw [Proof.Bignum.pow256_eq, eq] at qbound
  have nb' := Proof.Rsa.os2ip_high (bs := nb) (by omega_arith) hb
  rw [hnl, show 8 * k - 1 = 2 * (64 * (w / 2)) - 1 by omega_arith] at nb'
  have fb := Proof.Rsa.balanced_factor (by omega_arith) pbound qbound nb' he
  exact ⟨⟨fb.1, pbound⟩, fb.2, qbound⟩

end VG.Proof.Rsa.X86_64.Key
