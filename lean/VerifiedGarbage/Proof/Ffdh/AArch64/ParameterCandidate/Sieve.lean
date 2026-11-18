module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Base
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep

/-! ### `Ffdh.AArch64.ParameterCandidate.Halve`, which the modules that import this one used -/

section

/-!
# An FFDH parameter candidate on AArch64: `q = (p − 1) / 2`

`halveQ` (`halveQ_ok`): `aN := aN / 2` in place (`halfPass_ok`), and the
evenness of the result or'ed into `fBad`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The flag of an even `q`. -/
def evenFlag (q : Nat) : BitVec 64 := BitVec.ofNat 64 (1 - q % 2)

theorem evenFlag_zero (q : Nat) : evenFlag q = 0 ↔ q % 2 = 1 := by
  unfold evenFlag
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> rw [h] <;> decide

theorem low_bit_flag (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1 = BitVec.ofNat 64 (1 - x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, show BitVec.ofNat 64 1 = (1 : BitVec 64) from rfl, and1_toNat,
    show (1 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The halving's start: `x16 = x17 = aN`'s base, `x15` all ones. -/
theorem halveHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1])) s fun t =>
      (t.gpr .x16 = off B (slot w aN) ∧ t.gpr .x17 = off B (slot w aN) ∧ t.gpr .x15 = mask true ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep mmRegs s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  refine WP.mono (WP.keep [.x17, .x7, .x15] (Q := fun t => t.gpr .x16 = off B (slot w aN) ∧
      t.gpr .x17 = off B (slot w aN) ∧ t.gpr .x15 = mask true ∧ t.mem = s₂.mem) (by
    brun [h16, imm16 (show 0 < 65536 by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨a, b, c, d⟩, k₃⟩ => ?_
  exact ⟨⟨a, b, c, (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12), by rw [d, m₂, m₁]⟩,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `halveQ`: `q := c / 2` in `aN`, and its evenness or'ed into `fBad`. -/
theorem halveQ_ok {s : State} {p : PP} {w c : Nat} {v : BitVec 64} (h : PSt p w s)
    (hc : wv s.mem p.B (slot w aN) w = c) (hv : word s.mem p.B (8 * fBad) = v) :
    WP isa (seqs halveQ) s fun t =>
      PSt p w t ∧ wv t.mem p.B (slot w aN) w = c / 2 ∧ word t.mem p.B (8 * fBad) = v ||| evenFlag (c / 2) ∧
        Frm p.B [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hw1 := hws.w1
  have hw2 := hws.w2
  have h256 := hws.h256
  have sN := hws.sl (show aN < 16 by decide)
  unfold halveQ
  rw [List.cons_append]
  refine wp_seqs_append (a := _ :: halfPass) (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (halveHead_ok hws) fun s₁ ⟨⟨h16, h17, h15, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (halfPass_ok (mb := true) (hs.congr k₁.wr) h16 h17 h15 h12 hw1 (by omega_using [hw2]) (by omega_using [sN]) (by omega_using [sN])
    (.inl rfl)) fun s₂ ⟨hv₂, o₂, k₂⟩ => ?_
  simp only [ite_true] at hv₂
  rw [hm₁, hc] at hv₂
  rw [hm₁] at o₂
  have f₂a : Frm p.B [(slot w aN, 8 * (w + 2))] s.mem s₂.mem :=
    Frm.of_outside (o₂.mono (o' := slot w aN) (n' := 8 * (w + 2)) (by omega_using []) (by omega_using [])) (by simp)
  have f₂ : Frm p.B [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)] s.mem s₂.mem := f₂a.mono (by simp)
  have k12 := k₁.trans k₂
  have hmut : ∀ r ∈ [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)], KMut r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [KMut.ofSlot _ _ _, KMut.hdr (by decide)]
  have pmut : ∀ r ∈ [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)], PMut r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [PMut.ofSlot _ _ _, PMut.hdr (by decide)]
  have zz : ∀ r ∈ [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)], r.1 + r.2 ≤ p.Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [fBad] <;> omega_arith
  have hws₂ : Ws s₂ p.B p.Z w := hws.congr' f₂ hmut k12 (by decide)
  have hb₂ : word s₂.mem p.B (8 * fBad) = v := by
    rw [f₂a.word_eq (d := 8 * fBad) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot w aN (by decide))) (by simp only [fBad]; omega_using [])]
    exact hv
  have hlow : (word s₂.mem p.B (slot w aN)).toNat % 2 = c / 2 % 2 := by
    rw [← hv₂, ← wv_mod64 s₂.mem p.B (slot w aN) (n := w) (by omega_using [hw1]), Nat.mod_mod_of_dvd _ (by decide)]
  -- The flag.
  have hblk : WP isa (.block (ws ++ base aN .x16 ++ [ldh .x5 fBad, ld .x3 .x16, movi .x4 1,
      .logic .and .x .x3 .x3 .x4, .logic .eor .x .x3 .x3 .x4, .logic .orr .x .x5 .x5 .x3, sth .x5 fBad])) s₂
      (fun t => t.mem = s₂.mem.writeW (off p.B (8 * fBad)) (v ||| evenFlag (c / 2)) ∧ Keep mmRegs s₂ t) := by
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono hws₂.ws_ok fun s₃ ⟨⟨_, h11, m₃, _⟩, k₃⟩ => ?_
    refine WP.mono (base_ok aN .x16 ((k₃.gpr .x0 (by decide)).trans hws₂.x0) h11) fun s₄ ⟨⟨h16₄, m₄, _⟩, k₄⟩ => ?_
    have hs₄ := hs.congr ((k12.trans k₃).trans k₄).wr
    have h0₄ : s₄.gpr .x0 = p.B := ((k₃.trans k₄).gpr .x0 (by decide)).trans hws₂.x0
    have hfl : (word s₂.mem p.B (slot w aN) &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1 = evenFlag (c / 2) := by
      rw [low_bit_flag, hlow]; rfl
    refine WP.mono (WP.keep [.x5, .x3, .x4] (Q := fun t =>
        t.mem = s₂.mem.writeW (off p.B (8 * fBad)) (v ||| evenFlag (c / 2))) (by
      brun [h16₄, h0₄, m₄, m₃, hb₂, imm16 (show 1 < 65536 by decide), hdr_enc (show fBad < 32 by decide),
        hs₄.ld (d := 8 * fBad) (by simp only [fBad]; omega_using [h256]), hs₄.st (d := 8 * fBad) (by simp only [fBad]; omega_using [h256]),
        hs₄.ld (d := slot w aN) (by omega_using [sN]), hfl])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₅⟩ => ⟨hm, ((k₃.trans k₄).trans k₅).mono (by decide)⟩
  refine WP.mono hblk fun t ⟨hm, k₃⟩ => ?_
  have f₃' : Frm p.B [(8 * fBad, 8)] s₂.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fBad]; omega_using [])) (by simp)
  have f₃ : Frm p.B [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)] s₂.mem t.mem := f₃'.mono (by simp)
  have hf := f₂.trans f₃
  have k13 := k12.trans k₃
  refine ⟨h.step (hws.congr' hf hmut k13 (by decide)) hf pmut zz k13, ?_, by rw [hm, word_writeW_self], hf,
    k13.mono (by decide)⟩
  rw [f₃'.wv_eq (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Or.inr (hdr_lt_slot w aN (by decide))) (by omega_using [hn, sN])]
  exact hv₂

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on AArch64: the sieve

`tableWrite` (`tableWrite_ok`) writes RSA's table of small primes at
`aTab`; `sieve first` (`sieve_ok`) runs RSA's trial division on `aN` by
the table's first `4 (sieveWords first w)` entries, the whole division's
`4 (trialN w)` (512, or 1024 for `w > 16`) or, for `p` before `q` is
looked at, its first words' alone, and or's the mask of a divisor into
`fBad`. It stops after the first word of the table with a divisor (`stopN`,
the words it reads): a divisor among those is one among all
(`anyPre_stopN`), so the mask is that of all the words it was given.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-! ## Where the sieve stops -/

/-- A divisor among the first entries is one among more. -/
theorem anyPre_mono {c m n : Nat} (h : m ≤ n) (hm : anyPre c m = true) : anyPre c n = true := by
  unfold anyPre at hm ⊢
  rw [List.any_eq_true] at hm ⊢
  obtain ⟨i, hi, hd⟩ := hm
  exact ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi) h), hd⟩

/-- The words the sieve reads, of the table's first `N`: up to the first
with an entry dividing `c`. -/
def stopN (c : Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => if anyPre c (4 * stopN c N) = true then stopN c N else N + 1

theorem stopN_succ (c N : Nat) :
    stopN c (N + 1) = if anyPre c (4 * stopN c N) = true then stopN c N else N + 1 := rfl

theorem stopN_le (c : Nat) : ∀ N, stopN c N ≤ N
  | 0 => Nat.le_refl 0
  | N + 1 => by
    rw [stopN_succ]
    split
    · exact Nat.le_succ_of_le (stopN_le c N)
    · exact Nat.le_refl _

/-- It stops at the last word or at a divisor. -/
theorem stopN_end (c : Nat) : ∀ N, stopN c N = N ∨ anyPre c (4 * stopN c N) = true
  | 0 => .inl rfl
  | N + 1 => by
    by_cases h : anyPre c (4 * stopN c N) = true
    · rw [stopN_succ, ite_eq_left h]; exact .inr h
    · rw [stopN_succ, ite_eq_right h]; exact .inl rfl

theorem stopN_pos (c : Nat) : ∀ {N : Nat}, 0 < N → 0 < stopN c N
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | N + 1, _ => by
    by_cases h : anyPre c (4 * stopN c N) = true
    · rw [stopN_succ, ite_eq_left h]
      rcases Nat.eq_zero_or_pos (stopN c N) with h0 | h0
      · rw [h0, Nat.mul_zero, anyPre_zero] at h; exact absurd h Bool.false_ne_true
      · exact h0
    · rw [stopN_succ, ite_eq_right h]; exact Nat.succ_pos N

/-- Before it stops, no entry divides. -/
theorem stopN_before (c : Nat) : ∀ N k, k < stopN c N → anyPre c (4 * k) = false
  | 0, k, h => absurd h (Nat.not_lt_zero k)
  | N + 1, k, h => by
    by_cases hd : anyPre c (4 * stopN c N) = true
    · rw [stopN_succ, ite_eq_left hd] at h
      exact stopN_before c N k h
    · rw [stopN_succ, ite_eq_right hd] at h
      have hN : stopN c N = N := (stopN_end c N).resolve_right hd
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with hk | hk
      · exact stopN_before c N k (by rw [hN]; exact hk)
      · rw [hN] at hd; rw [hk]; exact Bool.eq_false_iff.mpr hd

/-- After word `k`: a divisor ends the sieve, and without one it goes on
while words are left. -/
theorem stopN_next {c N k : Nat} (hk : k < stopN c N) :
    (anyPre c (4 * (k + 1)) = true → k + 1 = stopN c N) ∧
      (anyPre c (4 * (k + 1)) = false → (k + 1 < stopN c N ↔ k + 1 < N)) := by
  have hle := stopN_le c N
  refine ⟨fun hd => ?_, fun hd => ⟨fun h => Nat.lt_of_lt_of_le h hle, fun h => ?_⟩⟩
  · rcases Nat.lt_or_ge (k + 1) (stopN c N) with h | h
    · rw [stopN_before c N (k + 1) h] at hd; exact absurd hd Bool.false_ne_true
    · omega_using [hk, h]
  · rcases stopN_end c N with he | he
    · rw [he]; exact h
    · rcases Nat.lt_or_ge (k + 1) (stopN c N) with h' | h'
      · exact h'
      · have e : k + 1 = stopN c N := by omega_using [hk, h']
        rw [← e, hd] at he; exact absurd he Bool.false_ne_true

/-- A divisor among the words read is one among all the words. -/
theorem anyPre_stopN (c N : Nat) : anyPre c (4 * stopN c N) = anyPre c (4 * N) := by
  rcases stopN_end c N with h | h
  · rw [h]
  · rw [h, anyPre_mono (Nat.mul_le_mul_left 4 (stopN_le c N)) h]

/-- RSA's table at `aTab`. -/
def TabOk (m : Mem) (B : Addr) (w : Nat) : Prop :=
  ∀ i < 256, word m B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i)

theorem tableWrite_ok {s : State} {p : PP} {w : Nat} (h : PSt p w s) (hT : slot w aTab + 2048 ≤ p.Z) :
    WP isa tableWrite s fun t =>
      PSt p w t ∧ TabOk t.mem p.B w ∧ Frm p.B [(slot w aTab, 2048)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.ws
  unfold tableWrite
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono hws.ws_ok fun s₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aTab .x9 ((k₁.gpr .x0 (by decide)).trans hws.x0) h11) fun s₂ ⟨⟨h9, m₂, _⟩, k₂⟩ => ?_
  refine WP.mono (tabWrites_ok (hws.scr.congr (k₁.trans k₂).wr) hT h9 256 (Nat.le_refl _))
    fun t ⟨htab, ho, k₃⟩ => ?_
  rw [m₂, m₁] at ho
  have hf : Frm p.B [(slot w aTab, 2048)] s.mem t.mem := Frm.of_outside ho (by simp)
  have k13 := (k₁.trans k₂).trans k₃
  exact ⟨h.step (hws.congr' hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k13
    (by decide)) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hT) k13, htab, hf, k13.mono (by decide)⟩

/-- The table's words the whole sieve divides by: 256 for `w > 16`, else
128. -/
def trialN (w : Nat) : Nat := if 17 ≤ w then 256 else 128

/-- The table's words `sieve first` divides by. -/
def sieveWords (first : Bool) (w : Nat) : Nat := if first then firstWords else trialN w

theorem sieveWords_false (w : Nat) : sieveWords false w = trialN w := rfl

theorem sieveWords_le (first : Bool) (w : Nat) : 1 ≤ sieveWords first w ∧ sieveWords first w ≤ 256 := by
  cases first
  · show 1 ≤ trialN w ∧ trialN w ≤ 256
    unfold trialN; split <;> omega_arith
  · exact (by decide : 1 ≤ firstWords ∧ firstWords ≤ 256)

/-- The first words are among the whole sieve's. -/
theorem sieveWords_trialN (first : Bool) (w : Nat) : sieveWords first w ≤ trialN w := by
  cases first
  · exact Nat.le_refl _
  · show firstWords ≤ trialN w
    unfold trialN firstWords; split <;> omega_arith

/-- The sieve's start: the table's base into `x9`, the counts. -/
theorem sieveInit_ok (first : Bool) {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block (ws ++ base aTab .x9 ++ sieveCount first ++ [movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1])) s
      fun t => (t.gpr .x9 = off B (slot w aTab + 8 * 0) ∧ t.gpr .x10 = BitVec.ofNat 64 (sieveWords first w) ∧
        t.gpr .x1 = 0 ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true ∧ t.mem = s.mem) ∧ Keep mmRegs s t := by
  rw [List.append_assoc, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aTab .x9 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h9, m₂, _⟩, k₂⟩ => ?_
  cases first
  · refine WP.mono (trialInit_ok s₂ ((k₂.gpr .x12 (by decide)).trans h12) h.w2)
      fun t ⟨⟨a, b, c, d, e⟩, k₃⟩ => ?_
    exact ⟨⟨by rw [k₃.gpr .x9 (by decide), h9, Nat.mul_zero, Nat.add_zero], a, b, c, d, by rw [e, m₂, m₁]⟩,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · show WP isa (.block ([movi .x10 firstWords, movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1] : List Instr)) s₂ _
    refine WP.mono (WP.keep [.x10, .x1, .x7, .x8] (Q := fun t => t.gpr .x10 = BitVec.ofNat 64 firstWords ∧
        t.gpr .x1 = 0 ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true ∧ t.mem = s₂.mem) (by brun) (by decide) (by decide)
      (by decide +kernel)) fun t ⟨⟨a, b, c, d, e⟩, k₃⟩ => ?_
    exact ⟨⟨by rw [k₃.gpr .x9 (by decide), h9, Nat.mul_zero, Nat.add_zero], a, b, c, d, by rw [e, m₂, m₁]⟩,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- After a word: the words left zeroed under the mask of a divisor. -/
theorem sieveStop_ok (s : State) {b : Bool} {v : BitVec 64} (h1 : s.gpr .x1 = mask b)
    (h8 : s.gpr .x8 = mask true) (h10 : s.gpr .x10 = v) :
    WP isa sieveStop s fun t => (t.gpr .x10 = (if b = true then 0 else v) ∧ t.mem = s.mem) ∧
      Keep [.x3, .x10] s t := by
  unfold sieveStop
  refine WP.mono (WP.keep [.x3, .x10] (Q := fun t =>
      t.gpr .x10 = s.gpr .x10 &&& (s.gpr .x1 ^^^ s.gpr .x8) ∧ t.mem = s.mem) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h, hm⟩, k⟩ => ⟨⟨?_, hm⟩, k⟩
  rw [h, h1, h8, h10, mask_true]
  cases b
  · rw [mask_false, show (0 : BitVec 64) ^^^ BitVec.allOnes 64 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    rfl
  · rw [mask_true, BitVec.xor_self, BitVec.and_zero]
    rfl

/-- A word of the table and the stop after it: `x10` is 0 after a word with
a divisor, else one less. -/
theorem sieveWord_ok {s₀ : State} {B : Addr} {Z w T c k : Nat} (hc : wv s₀.mem B (slot w aN) w = c)
    (hT : T + 2048 ≤ Z) (hk : k < 256)
    (htab : ∀ i < 256, word s₀.mem B (T + 8 * i) = BitVec.ofNat 64 (tabWord i)) {t : State}
    (hI : TLInv s₀ B Z w t) (h9 : t.gpr .x9 = off B (T + 8 * k)) (hf : t.gpr .x1 = mask (anyPre c (4 * k))) :
    WP isa (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)) ++
      ([sieveStop] : List (Prog isa)))) t fun t' =>
      TLInv s₀ B Z w t' ∧ t'.gpr .x9 = off B (T + 8 * (k + 1)) ∧ t'.gpr .x1 = mask (anyPre c (4 * (k + 1))) ∧
        t'.gpr .x10 = if anyPre c (4 * (k + 1)) = true then 0 else t.gpr .x10 - BitVec.ofNat 64 1 := by
  refine wp_seqs_append (by simp) (by simp) (WP.mono (tlIter_ok hc hT hk htab hI h9 hf)
    fun t₁ ⟨⟨hI₁, h9₁, h1₁⟩, h10₁⟩ => ?_)
  rw [seqs_one]
  refine WP.mono (sieveStop_ok t₁ h1₁ hI₁.x8 h10₁) fun t' ⟨⟨h10, hm⟩, k'⟩ => ?_
  exact ⟨⟨hI₁.ws.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k' (by decide),
    (k'.gpr .x7 (by decide)).trans hI₁.x7, (k'.gpr .x8 (by decide)).trans hI₁.x8, hm.trans hI₁.mem,
    (hI₁.keep.trans k').mono (by decide)⟩, (k'.gpr .x9 (by decide)).trans h9₁,
    (k'.gpr .x1 (by decide)).trans h1₁, h10⟩

theorem sieve_eq (first : Bool) : sieve first = ([
    .block (ws ++ base aTab .x9 ++ sieveCount first ++ [movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1]),
    .loop (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)) ++
      ([sieveStop] : List (Prog isa)))) (.nonzero .x .x10),
    .block [ldh .x5 fBad, .logic .orr .x .x5 .x5 .x1, sth .x5 fBad]] : List (Prog isa)) := rfl

/-- `sieve`: the mask of an entry of the table's first `4 (sieveWords
first w)` dividing `aN` or'ed into `fBad`. -/
theorem sieve_ok (first : Bool) {s : State} {p : PP} {w c : Nat} {v : BitVec 64} (h : PSt p w s)
    (hT : slot w aTab + 2048 ≤ p.Z) (htab : TabOk s.mem p.B w) (hc : wv s.mem p.B (slot w aN) w = c)
    (hv : word s.mem p.B (8 * fBad) = v) :
    WP isa (seqs (sieve first)) s fun t =>
      PSt p w t ∧ word t.mem p.B (8 * fBad) = v ||| mask (anyPre c (4 * sieveWords first w)) ∧
        Frm p.B [(8 * fBad, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have h256 := hws.h256
  rw [sieve_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (sieveInit_ok first hws) fun s₁ ⟨⟨h9₁, h10₁, h1₁, h7₁, h8₁, hm₁⟩, k₁⟩ => ?_)
  have hws₁ : Ws s₁ p.B p.Z w := hws.congr' (rs := []) (by rw [hm₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
  have htab₁ : ∀ i < 256, word s₁.mem p.B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i) := fun i hi => by
    rw [hm₁]; exact htab i hi
  have hc₁ : wv s₁.mem p.B (slot w aN) w = c := by rw [hm₁]; exact hc
  have hN : sieveWords first w ≤ 256 ∧ 1 ≤ sieveWords first w :=
    ⟨(sieveWords_le first w).2, (sieveWords_le first w).1⟩
  generalize sieveWords first w = N at hN h10₁ ⊢
  have hSle := stopN_le c N
  refine WP.seq (WP.mono (count_loop (cr := .x10) (stopN_pos c (show 0 < N by omega_arith))
    (fun k t => TLInv s₁ p.B p.Z w t ∧ t.gpr .x9 = off p.B (slot w aTab + 8 * k) ∧
      t.gpr .x1 = mask (anyPre c (4 * k)) ∧
      (anyPre c (4 * k) = false → t.gpr .x10 = BitVec.ofNat 64 (N - k)))
    (fun k hk t ⟨hI, h9, hf, h10⟩ => ?_)
    ⟨⟨hws₁, h7₁, h8₁, rfl, Keep.refl _ _⟩, h9₁, by rw [h1₁, Nat.mul_zero, anyPre_zero]; rfl,
      fun _ => by rw [h10₁, Nat.sub_zero]⟩)
    fun s₄ ⟨hI₄, _, h1₄, _⟩ => ?_)
  · -- A word: the sieve goes on without a divisor, while words are left.
    have h10k := h10 (stopN_before c (N) k hk)
    obtain ⟨nxt, nxf⟩ := stopN_next hk
    have e10 : BitVec.ofNat 64 (N - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (k + 1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [hk, hSle, hN.1]
    refine WP.mono (sieveWord_ok hc₁ hT (by omega_using [hk, hSle, hN.1]) htab₁ hI h9 hf)
      fun t' ⟨hI', h9', h1', h10'⟩ => ⟨⟨hI', h9', h1', fun hd => ?_⟩, ?_⟩
    · rw [h10', ite_eq_right (by rw [hd]; exact Bool.false_ne_true), h10k, e10]
    · rcases Bool.eq_false_or_eq_true (anyPre c (4 * (k + 1))) with hd | hd
      · rw [h10', ite_eq_left hd]
        exact ⟨fun h => absurd rfl h, fun h => absurd (nxt hd) h⟩
      · have hi := nxf hd
        rw [h10', ite_eq_right (by rw [hd]; exact Bool.false_ne_true), h10k, e10, BitVec.toNat_ofNat]
        omega_using [hk, hSle, hN.1, hi]
  rw [anyPre_stopN] at h1₄
  have hm₄ : s₄.mem = s.mem := hI₄.mem.trans hm₁
  have hv₄ : s₄.mem.readW (off p.B (8 * fBad)) 64 = v := by rw [hm₄]; exact hv
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.mem = s₄.mem.writeW (off p.B (8 * fBad))
      (v ||| mask (anyPre c (4 * N))))
    (by
      brun [hI₄.ws.x0, hdr_enc (show fBad < 32 by decide), hI₄.ws.scr.ld (d := 8 * fBad) (by simp only [fBad]; omega_arith),
        hI₄.ws.scr.st (d := 8 * fBad) (by simp only [fBad]; omega_arith), hv₄, h1₄])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₅⟩ => ?_
  have hf : Frm p.B [(8 * fBad, 8)] s.mem t.mem := by
    rw [hm, hm₄]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fBad]; omega_arith)) (by simp)
  have k15 := (k₁.trans hI₄.keep).trans k₅
  refine ⟨h.step (hws.congr' hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide)) k15
    (by decide)) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
    (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fBad]; omega_arith) k15, by rw [hm, word_writeW_self], hf,
    k15.mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.ParameterCandidate
