module
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFast

import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
import VerifiedGarbage.Proof.Rsa.Ranges

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
  w4 : 4 ≤ w
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
  refine wsa (by simp [Impl.Rsa.X86_64.Keys.loadA]) (by simp) (WP.mono (loadA_ok (h₁.ws r)
    (j := Impl.Rsa.X86_64.WordDivide.aD) (sPtr := sD) (sLen := sDlen) (by decide) (by decide) (by decide)
    (by rw [h₁.hdr _ (by decide) (by decide)]; exact hpd) (by rw [h₁.hdr _ (by decide) (by decide)]; exact hdl)
    (h₁.src srcD) rfl hd1 hdk) fun t₂ ⟨v₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.frm (Frm.of_outside o₂ (List.mem_singleton_self _))
    (by simp only [List.mem_singleton, forall_eq]; exact away_slot w (by decide) (.inl (by decide)) (Nat.le_refl _))
    (by simp only [List.mem_singleton, forall_eq]; exact sl 5 (by decide)) (k₂.mono (by decide))
  have e₂ : ∀ j, j = 1 ∨ j = 4 ∨ j = 9 → wv t₂.mem B (slot w j) w = wv t₁.mem B (slot w j) w := fun j hj => by
    have := hZ
    refine o₂.wv ?_ (by rcases hj with rfl | rfl | rfl <;> simp only [slot_eq] at * <;> omega_arith)
    simp only [Impl.Rsa.X86_64.WordDivide.aD]
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
    simp only [Impl.Rsa.X86_64.WordDivide.aR, Impl.Rsa.X86_64.WordDivide.aD, Impl.Rsa.X86_64.WordDivide.aM] at q v₂
    rw [v₂, d₂] at q
    have pos : 0 < wv t.mem B (slot w aM) w := by have := Nat.one_le_two_pow (n := 64 * (w / 2) - 1); omega_arith
    have lt : Spec.Rsa.os2ip db % wv t.mem B (slot w aM) w < 2 ^ (64 * w) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ pos)
        (Nat.le_trans (Nat.le_of_lt hlt) (Nat.pow_le_pow_right (by decide) (by omega_arith)))
    rw [wv_of_lt _ _ _ (Nat.le_succ w) (by rw [q]; exact lt), q]
  · have ex : wv t₃.mem B (slot w aX) w = wv t.mem B (slot w aX) w := by
      rw [wv_norm f₃ hn hZ (j := aX) (.inl rfl), e₂ aX (by decide), e₁ aX (.inl rfl)]
    rw [m₅, word_writeW_self, ex]; rfl

end

end VG.Proof.Rsa.X86_64.Key
