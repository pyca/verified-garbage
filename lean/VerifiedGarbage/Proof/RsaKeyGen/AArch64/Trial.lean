import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable

/-!
# A candidate on AArch64: trial division

`trial` writes the table at `aTab` (`tabWrites_ok`), then runs `trialEntry`
for the four entries of each of its first `N` words (`N = 256` for `w > 16`,
128 otherwise), or'ing the masks of the entries that divide `c` into `x1`:
`x1` is not zero iff `trialAny N c` (`trial_ok`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN)

/-- Trial division by the first `m` entries of the table. -/
def anyPre (c m : Nat) : Bool := (List.range m).any fun i => c % tabEntry i == 0

theorem anyPre_succ (c m : Nat) : anyPre c (m + 1) = (anyPre c m || c % tabEntry m == 0) := by
  unfold anyPre; rw [List.range_succ, List.any_append]; simp

theorem anyPre_zero (c : Nat) : anyPre c 0 = false := rfl

theorem trial_decide_beq (a b : Nat) : decide (a = b) = (a == b) :=
  Bool.eq_iff_iff.mpr ⟨fun h => beq_iff_eq.mpr (of_decide_eq_true h), fun h => decide_eq_true (beq_iff_eq.mp h)⟩

theorem trial_mask_ne (b : Bool) : (mask b != 0) = b := by cases b <;> decide

/-- The counts: `x10 := N`, `x1 := 0`, `x7 := 0` and `x8` all ones. -/
theorem trialInit_ok (t : State) {w : Nat} (h12 : t.gpr .x12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 24) :
    WP isa (.block [movi .x3 128, movi .x4 256, movi .x5 17, .subs .x .x6 .x12 .x5, .csel .x .x10 .x4 .x3,
      movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1]) t fun t' =>
      (t'.gpr .x10 = BitVec.ofNat 64 (if 17 ≤ w then 256 else 128) ∧ t'.gpr .x1 = 0 ∧ t'.gpr .x7 = 0 ∧
        t'.gpr .x8 = mask true ∧ t'.mem = t.mem) ∧
      Keep [.x3, .x4, .x5, .x6, .x10, .x1, .x7, .x8] t t' := by
  refine WP.keep [.x3, .x4, .x5, .x6, .x10, .x1, .x7, .x8] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h12]
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (BitVec.setWidth 64 17#16 : BitVec 64).toNat = 17 from rfl, show true.toNat = 1 from rfl]
  split <;> rename_i h1 <;> split <;> rename_i h2 <;>
    simp only [decide_eq_true_eq] at h1
  · rfl
  · omega
  · omega
  · rfl

/-- What the loop keeps, from the state `s₀` after the table. -/
structure TLInv (s₀ : State) (B : Addr) (Z w : Nat) (t : State) : Prop where
  ws : Ws t B Z w
  x7 : t.gpr .x7 = 0
  x8 : t.gpr .x8 = mask true
  mem : t.mem = s₀.mem
  keep : Keep mmRegs s₀ t

/-- One entry of table word `k`, in the loop. -/
theorem tlEntry_ok {s₀ : State} {B : Addr} {Z w c k j : Nat} (hc : wv s₀.mem B (slot w aN) w = c) (hk : k < 256)
    (hj : j < 4) {t : State} (hI : TLInv s₀ B Z w t) (hf : t.gpr .x1 = mask (anyPre c (4 * k + j)))
    (h17 : t.gpr .x17 = BitVec.ofNat 64 (tabWord k)) :
    WP isa (seqs (trialEntry j)) t fun t' => TLInv s₀ B Z w t' ∧
      t'.gpr .x1 = mask (anyPre c (4 * k + j + 1)) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x12, .x13, .x14, .x15, .x16] t t' :=
  WP.mono (trialEntry_ok hI.ws hk hj h17 hI.x7 hI.x8) fun t' ⟨h1, hm, k'⟩ =>
    ⟨⟨hI.ws.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k' (by decide), (k'.gpr .x7 (by decide)).trans hI.x7,
      (k'.gpr .x8 (by decide)).trans hI.x8, hm.trans hI.mem, (hI.keep.trans k').mono (by decide)⟩,
      by rw [h1, hf, hI.mem, hc, trial_decide_beq, trial_mask_or, anyPre_succ], k'⟩

/-- Word `k` of the table at `T` into `x17`, and `x9` to the next. -/
theorem tlLoad_ok {s₀ : State} {B : Addr} {Z w T k : Nat} (hT : T + 2048 ≤ Z) (hk : k < 256)
    (htab : ∀ i < 256, word s₀.mem B (T + 8 * i) = BitVec.ofNat 64 (tabWord i)) {t : State}
    (hI : TLInv s₀ B Z w t) (h9 : t.gpr .x9 = off B (T + 8 * k)) :
    WP isa (.block [ld .x17 .x9, next .x9]) t fun t' =>
      (t'.gpr .x17 = BitVec.ofNat 64 (tabWord k) ∧ t'.gpr .x9 = off B (T + 8 * (k + 1)) ∧ t'.mem = t.mem) ∧
      Keep [.x17, .x9] t t' := by
  have hld : InRegions (t.rd ++ t.wr) (off B (T + 8 * k)) 8 := hI.ws.scr.ld (by omega)
  refine WP.keep [.x17, .x9] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h9, hld, hI.mem, htab k hk]
  rw [Nat.mul_succ, Nat.add_assoc]

/-- One word of the table: its four entries, and the count. -/
theorem tlIter_ok {s₀ : State} {B : Addr} {Z w T c k : Nat} (hc : wv s₀.mem B (slot w aN) w = c)
    (hT : T + 2048 ≤ Z) (hk : k < 256)
    (htab : ∀ i < 256, word s₀.mem B (T + 8 * i) = BitVec.ofNat 64 (tabWord i)) {t : State}
    (hI : TLInv s₀ B Z w t) (h9 : t.gpr .x9 = off B (T + 8 * k)) (hf : t.gpr .x1 = mask (anyPre c (4 * k))) :
    WP isa (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)))) t fun t' =>
      (TLInv s₀ B Z w t' ∧ t'.gpr .x9 = off B (T + 8 * (k + 1)) ∧ t'.gpr .x1 = mask (anyPre c (4 * (k + 1)))) ∧
      t'.gpr .x10 = t.gpr .x10 - BitVec.ofNat 64 1 := by
  simp only [List.append_assoc, List.cons_append]
  refine WP.seq (WP.mono (tlLoad_ok hT hk htab hI h9) fun t₁ ⟨⟨h17₁, h9₁, hm₁⟩, k₁⟩ => ?_)
  have hI₁ : TLInv s₀ B Z w t₁ := ⟨hI.ws.congr' (rs := []) (fun x _ => by rw [hm₁]) (by simp) k₁ (by decide),
    (k₁.gpr .x7 (by decide)).trans hI.x7, (k₁.gpr .x8 (by decide)).trans hI.x8, hm₁.trans hI.mem,
    (hI.keep.trans k₁).mono (by decide)⟩
  have hf₁ : t₁.gpr .x1 = mask (anyPre c (4 * k + 0)) := (k₁.gpr .x1 (by decide)).trans hf
  have ne : ∀ j, trialEntry j ≠ [] := fun j => by unfold trialEntry; exact List.cons_ne_nil _ _
  refine wp_seqs_append (ne 0) (by simp) (WP.mono (tlEntry_ok hc hk (by decide) hI₁ hf₁ h17₁)
    fun t₂ ⟨hI₂, hf₂, k₂⟩ => ?_)
  rw [show 4 * k + 0 + 1 = 4 * k + 1 by omega] at hf₂
  refine wp_seqs_append (ne 1) (by simp) (WP.mono (tlEntry_ok hc hk (by decide) hI₂ hf₂
    ((k₂.gpr .x17 (by decide)).trans h17₁)) fun t₃ ⟨hI₃, hf₃, k₃⟩ => ?_)
  refine wp_seqs_append (ne 2) (by simp) (WP.mono (tlEntry_ok hc hk (by decide) hI₃ (by rw [hf₃])
    ((k₃.gpr .x17 (by decide)).trans ((k₂.gpr .x17 (by decide)).trans h17₁))) fun t₄ ⟨hI₄, hf₄, k₄⟩ => ?_)
  refine wp_seqs_append (ne 3) (by simp) (WP.mono (tlEntry_ok hc hk (by decide) hI₄ (by rw [hf₄])
    ((k₄.gpr .x17 (by decide)).trans ((k₃.gpr .x17 (by decide)).trans ((k₂.gpr .x17 (by decide)).trans h17₁))))
    fun t₅ ⟨hI₅, hf₅, k₅⟩ => ?_)
  have k25 := (k₂.trans k₃).trans (k₄.trans k₅)
  simp only [seqs]
  refine WP.mono (dec_ok t₅ .x10) fun t' ⟨⟨h10, hm', _⟩, k'⟩ =>
    ⟨⟨⟨hI₅.ws.congr' (rs := []) (fun x _ => by rw [hm']) (by simp) k' (by decide), (k'.gpr .x7 (by decide)).trans hI₅.x7,
      (k'.gpr .x8 (by decide)).trans hI₅.x8, hm'.trans hI₅.mem, (hI₅.keep.trans k').mono (by decide)⟩,
      by rw [k'.gpr .x9 (by decide), k25.gpr .x9 (by decide), h9₁],
      by rw [k'.gpr .x1 (by decide), hf₅, show 4 * k + 3 + 1 = 4 * (k + 1) by omega]⟩,
      by rw [h10, k25.gpr .x10 (by decide), k₁.gpr .x10 (by decide)]⟩

/-- `trial`: `x1` is not zero iff one of the first `4 N` entries of the table
divides `c`, `N = 256` for `w > 16` and 128 otherwise. -/
theorem trial_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hT : slot w aTab + 2048 ≤ Z)
    (hw4 : 4 ≤ w) (hw64 : w ≤ 64) :
    WP isa (seqs trial) s fun t =>
      (t.gpr .x1 != 0) = trialAny (if 17 ≤ w then 256 else 128) (wv s.mem B (slot w aN) w) ∧
      Ws t B Z w ∧ Frm B [(slot w aTab, 2048)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hTa : slot w aN + 8 * w ≤ slot w aTab := by unfold slot aN aTab; omega
  unfold trial
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12₁, h11₁, hm₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aTab .x9 ((k₁.gpr .x0 (by decide)).trans h.x0) h11₁) fun s₂ ⟨⟨h9₂, hm₂, _⟩, k₂⟩ => ?_
  refine WP.mono (tabWrites_ok (h.scr.congr (k₁.trans k₂).wr) hT h9₂ 256 (Nat.le_refl _)) fun s₃ ⟨htab₃, ho₃, k₃⟩ => ?_
  rw [hm₂, hm₁] at ho₃
  have h12₃ : s₃.gpr .x12 = BitVec.ofNat 64 w := (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12₁)
  refine WP.mono (trialInit_ok s₃ h12₃ h.w2) fun s₄ ⟨⟨h10₄, h1₄, h7₄, h8₄, hm₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hf₄ : Frm B [(slot w aTab, 2048)] s.mem s₄.mem := by rw [hm₄]; exact Frm.of_outside ho₃ (by simp)
  have h₄ : Ws s₄ B Z w := h.congr' hf₄ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact KMut.ofSlot w aTab _) k14 (by decide)
  have htab₄ : ∀ i < 256, word s₄.mem B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i) := fun i hi => by
    rw [hm₄]; exact htab₃ i hi
  have hc₄ : wv s₄.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
    rw [hm₄, ho₃.wv (Or.inl hTa) (by omega)]
  have h9₄ : s₄.gpr .x9 = off B (slot w aTab + 8 * 0) := by
    rw [k₄.gpr .x9 (by decide), k₃.gpr .x9 (by decide), h9₂, Nat.mul_zero, Nat.add_zero]
  generalize hNdef : (if 17 ≤ w then 256 else 128) = N at h10₄ ⊢
  have hN : N ≤ 256 ∧ 1 ≤ N := by rw [← hNdef]; split <;> omega
  refine WP.mono (wp_countdown (N := N) (by omega) (by omega) (fun k t => TLInv s₄ B Z w t ∧
      t.gpr .x9 = off B (slot w aTab + 8 * k) ∧ t.gpr .x1 = mask (anyPre (wv s.mem B (slot w aN) w) (4 * k)))
    (fun k hk t ⟨hI, h9, hf⟩ _ => tlIter_ok hc₄ hT (by omega) htab₄ hI h9 hf)
    ⟨⟨h₄, h7₄, h8₄, rfl, Keep.refl _ _⟩, h9₄, by rw [h1₄, Nat.mul_zero, anyPre_zero]; rfl⟩ h10₄) fun t ⟨hI, _, hf⟩ => ?_
  refine ⟨by rw [hf, trial_mask_ne]; rfl, hI.ws, by rw [hI.mem]; exact hf₄, (k14.trans hI.keep).mono (by decide)⟩

end VG.Proof.RsaKeyGen.AArch64
