module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeInput
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ProbablePrime
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial

/-! Trial division to the first divisor: RSA's, a word of the table at a time, and it
preserves the generation inputs and tape cursor. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.RsaKeyGen VG.Impl.RsaKeyGen

/-! ## The words the loop runs -/

/-- The words of a table of `T` the loop runs for the candidate `c`: up to the
first after which an entry has divided `c`. -/
def earlyWords (c : Nat) : Nat → Nat
  | 0 => 0
  | T + 1 => if anyPre c (4 * T) then earlyWords c T else T + 1

theorem anyPre_mono {c m n : Nat} (h : m ≤ n) (hm : anyPre c m = true) : anyPre c n = true := by
  unfold anyPre at hm ⊢
  rw [List.any_eq_true] at hm ⊢
  obtain ⟨i, hi, hd⟩ := hm
  exact ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi) h), hd⟩

theorem lt_earlyWords {c : Nat} : ∀ {T j : Nat}, j < earlyWords c T ↔ j < T ∧ anyPre c (4 * j) = false
  | 0, j => by simp [earlyWords]
  | T + 1, j => by
    rw [earlyWords]
    by_cases hT : anyPre c (4 * T) = true
    · simp only [hT, ↓reduceIte]
      rw [lt_earlyWords (T := T)]
      refine ⟨fun ⟨a, b⟩ => ⟨Nat.lt_succ_of_lt a, b⟩, fun ⟨a, b⟩ => ⟨?_, b⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp a with h | rfl
      · exact h
      · rw [hT] at b; exact absurd b (by decide)
    · simp only [hT, Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun a => ⟨a, ?_⟩, fun ⟨a, _⟩ => a⟩
      cases hj : anyPre c (4 * j)
      · rfl
      · exact absurd (anyPre_mono (show 4 * j ≤ 4 * T by omega_using [a]) hj) hT

theorem earlyWords_le (c T : Nat) : earlyWords c T ≤ T := by
  rcases Nat.lt_or_ge T (earlyWords c T) with h | h
  · exact absurd (lt_earlyWords.mp h).1 (Nat.lt_irrefl _)
  · exact h

theorem earlyWords_pos (c : Nat) {T : Nat} (hT : 0 < T) : 0 < earlyWords c T :=
  lt_earlyWords.mpr ⟨hT, rfl⟩

/-- Stopping early finds what the whole table does. -/
theorem anyPre_earlyWords (c T : Nat) : anyPre c (4 * earlyWords c T) = anyPre c (4 * T) := by
  rcases Nat.lt_or_eq_of_le (earlyWords_le c T) with h | h
  · have hs : anyPre c (4 * earlyWords c T) = true := by
      cases hj : anyPre c (4 * earlyWords c T)
      · exact absurd (lt_earlyWords.mpr ⟨h, hj⟩) (Nat.lt_irrefl _)
      · rfl
    rw [hs, anyPre_mono (show 4 * earlyWords c T ≤ 4 * T by omega_using [h]) hs]
  · rw [h]

/-! ## A word of the table -/

/-- The count cleared under the mask of a divisor. -/
theorem earlyStop_ok (t : State) {b : Bool} (h1 : t.gpr .x1 = mask b) (h8 : t.gpr .x8 = mask true) :
    WP isa (.block [.logic .eor .x .x3 .x1 .x8, .logic .and .x .x10 .x10 .x3]) t fun t' =>
      (t'.gpr .x10 = (if b then 0 else t.gpr .x10) ∧ t'.mem = t.mem) ∧ Keep [.x3, .x10] t t' := by
  refine WP.keep [.x3, .x10] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h1, h8]
  cases b
  · simp only [mask_false, mask_true, Bool.false_eq_true, ↓reduceIte]
    exact BitVec.and_allOnes
  · simp [mask_true]

theorem trialWord_ne : Impl.Dsa.AArch64.Generation.trialWord ≠ [] := by
  unfold Impl.Dsa.AArch64.Generation.trialWord
  simp only [List.append_assoc, List.singleton_append]
  exact List.cons_ne_nil _ _

/-- One word of the table, `k` of `T`, and the count: zero if one of the
entries so far divides `c`. -/
theorem earlyIter_ok {s₀ : State} {B : Addr} {Z w T N c k : Nat} (hc : wv s₀.mem B (slot w aN) w = c)
    (hT : T + 2048 ≤ Z) (hk : k < N) (hN : N ≤ 256)
    (htab : ∀ i < 256, word s₀.mem B (T + 8 * i) = BitVec.ofNat 64 (tabWord i)) {t : State}
    (hI : TLInv s₀ B Z w t) (h9 : t.gpr .x9 = off B (T + 8 * k)) (hf : t.gpr .x1 = mask (anyPre c (4 * k)))
    (h10 : t.gpr .x10 = BitVec.ofNat 64 (N - k)) :
    WP isa (seqs (Impl.Dsa.AArch64.Generation.trialWord ++
      ([.block [.logic .eor .x .x3 .x1 .x8, .logic .and .x .x10 .x10 .x3]] : List (Prog isa)))) t fun t' =>
      TLInv s₀ B Z w t' ∧ t'.gpr .x9 = off B (T + 8 * (k + 1)) ∧ t'.gpr .x1 = mask (anyPre c (4 * (k + 1))) ∧
      t'.gpr .x10 = (if anyPre c (4 * (k + 1)) then 0 else BitVec.ofNat 64 (N - (k + 1))) := by
  refine wp_seqs_append trialWord_ne (by simp)
    (WP.mono (tlIter_ok hc hT (by omega_using [hk, hN]) htab hI h9 hf) fun t₁ ⟨⟨hI₁, h9₁, hf₁⟩, h10₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (earlyStop_ok t₁ hf₁ hI₁.x8) fun t' ⟨⟨h10', hm'⟩, k'⟩ => ?_
  refine ⟨⟨hI₁.ws.congr' (rs := []) (fun x _ => by rw [hm']) (by simp) k' (by decide),
    (k'.gpr .x7 (by decide)).trans hI₁.x7, (k'.gpr .x8 (by decide)).trans hI₁.x8, hm'.trans hI₁.mem,
    (hI₁.keep.trans k').mono (by decide)⟩, (k'.gpr .x9 (by decide)).trans h9₁,
    (k'.gpr .x1 (by decide)).trans hf₁, ?_⟩
  rw [h10', h10₁, h10]
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hk, hN]

/-- Whether the loop runs another word after word `k`. -/
theorem early_cond {c T k : Nat} (hk : k < earlyWords c T) (hT : T ≤ 256) :
    ((if anyPre c (4 * (k + 1)) then (0 : BitVec 64) else BitVec.ofNat 64 (T - (k + 1))) != 0) =
      decide (k + 1 < earlyWords c T) := by
  have hkT := (lt_earlyWords.mp hk).1
  cases hb : anyPre c (4 * (k + 1))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [bne, ofNat64_beq_zero (by omega_using [hT])]
    by_cases h : k + 1 < T
    · rw [decide_eq_false (by omega_using [h]), decide_eq_true (lt_earlyWords.mpr ⟨h, hb⟩)]; rfl
    · rw [decide_eq_true (by omega_using [h]), decide_eq_false (fun h' => h (lt_earlyWords.mp h').1)]; rfl
  · simp only [↓reduceIte]
    rw [decide_eq_false (fun h' => by
      have := (lt_earlyWords.mp h').2; rw [hb] at this; exact absurd this (by decide))]
    rfl

/-- `trialEarly`: as `trial_ok`, `x1` is not zero iff one of the first `4 N`
entries of the table divides `c`. -/
theorem trialEarly_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hT : slot w aTab + 2048 ≤ Z) :
    WP isa (seqs Impl.Dsa.AArch64.Generation.trialEarly) s fun t =>
      (t.gpr .x1 != 0) = trialAny (if 17 ≤ w then 256 else 128) (wv s.mem B (slot w aN) w) ∧
      Ws t B Z w ∧ Frm B [(slot w aTab, 2048)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hTa : slot w aN + 8 * w ≤ slot w aTab := by unfold slot aN aTab; omega
  unfold Impl.Dsa.AArch64.Generation.trialEarly
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
    rw [hm₄, ho₃.wv (Or.inl hTa) (by omega_using [hT, hn, hTa])]
  have h9₄ : s₄.gpr .x9 = off B (slot w aTab + 8 * 0) := by
    rw [k₄.gpr .x9 (by decide), k₃.gpr .x9 (by decide), h9₂, Nat.mul_zero, Nat.add_zero]
  generalize hNdef : (if 17 ≤ w then 256 else 128) = N at h10₄ ⊢
  have hN : N ≤ 256 ∧ 1 ≤ N := by rw [← hNdef]; split <;> omega_using []
  generalize hcdef : wv s.mem B (slot w aN) w = c at hc₄ ⊢
  refine WP.mono (VG.Proof.RsaOaep.AArch64.count_loop (cr := .x10) (n := earlyWords c N)
    (earlyWords_pos c (by omega_using [hN])) (fun k t => TLInv s₄ B Z w t ∧
      t.gpr .x9 = off B (slot w aTab + 8 * k) ∧ t.gpr .x1 = mask (anyPre c (4 * k)) ∧
      (k < earlyWords c N → t.gpr .x10 = BitVec.ofNat 64 (N - k)))
    (fun k hk t ⟨hI, h9, hf, h10⟩ => WP.mono (earlyIter_ok hc₄ hT (Nat.lt_of_lt_of_le hk (earlyWords_le c N)) hN.1
      htab₄ hI h9 hf (h10 hk)) fun t' ⟨hI', h9', hf', h10'⟩ => ⟨⟨hI', h9', hf', fun hk' => by
        rw [h10', (lt_earlyWords.mp hk').2]; rfl⟩, by
        rw [h10']
        exact (early_cond hk hN.1).trans
          (decide_eq_decide.mpr ⟨fun a => Nat.ne_of_lt a, fun a => by omega_using [a, hk]⟩)⟩)
    ⟨⟨h₄, h7₄, h8₄, rfl, Keep.refl _ _⟩, h9₄, by rw [h1₄, Nat.mul_zero, anyPre_zero]; rfl,
      fun _ => by rw [h10₄, Nat.sub_zero]⟩) fun t ⟨hI, _, hf, _⟩ => ?_
  refine ⟨by rw [hf, trial_mask_ne, anyPre_earlyWords]; rfl, hI.ws, by rw [hI.mem]; exact hf₄,
    (k14.trans hI.keep).mono (by decide)⟩

def primeTrialRanges (w : Nat) : List (Nat × Nat) := [(slot w aTab, 2048)]

theorem primeTrial_ok {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeInput P used s) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w) :
    WP isa (seqs Impl.Dsa.AArch64.Generation.trialEarly) s fun t =>
      isa.eval (.zero .x .x1) t = some (!Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength P.N) P.N) ∧
      PrimeInput P used t ∧ Frm P.B (primeTrialRanges P.w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (trialEarly_ok h.ws hz)
    fun t ⟨hflag, ht, hf, hk⟩ => ?_
  rw [h.n, VG.Proof.Dsa.Generation.trialAny_dsa hn hpolicy] at hflag
  have hn' : wv t.mem P.B (slot P.w aN) P.w = P.N := by
    rw [hf.wv_eq (by intro r hr; rw [List.mem_singleton.mp hr]; left; simp only [slot, hdrBytes, aN, aTab]; omega_arith)
      (by have := h.ws.scr.nowrap; have := h.ws.sl (show aN < 16 by decide); omega_arith)]
    exact h.n
  have hi := h.advance ht hn' hf hk (by intro r hr; rw [List.mem_singleton.mp hr]; exact hz)
    (by
      intro j hj r hr; rw [List.mem_singleton.mp hr]
      have hj32 : j < 32 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      left; simp only [slot, hdrBytes, aTab]; omega_arith)
  refine ⟨?_, hi, hf, hk⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
  rw [← hflag]
  simp only [bne_eq, Bool.not_not]

end VG.Proof.Dsa.AArch64.Generation
