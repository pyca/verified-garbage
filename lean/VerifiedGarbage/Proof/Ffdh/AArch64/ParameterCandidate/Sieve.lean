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

/-!
# An FFDH parameter candidate on AArch64: the sieve

`tableWrite` (`tableWrite_ok`) writes RSA's table of small primes at
`aTab`; `sieve` (`sieve_ok`) runs RSA's trial division by its first
`4 (trialN w)` entries (512, or 1024 for `w > 16`) on `aN`, and or's the
mask of a divisor into `fBad`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

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

/-- The table's words the sieve divides by: 256 for `w > 16`, else 128. -/
def trialN (w : Nat) : Nat := if 17 ≤ w then 256 else 128

/-- The sieve's start: the table's base into `x9`, the counts. -/
theorem sieveInit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block (ws ++ base aTab .x9 ++ [movi .x3 128, movi .x4 256, movi .x5 17, .subs .x .x6 .x12 .x5,
      .csel .x .x10 .x4 .x3, movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1])) s
      fun t => (t.gpr .x9 = off B (slot w aTab + 8 * 0) ∧ t.gpr .x10 = BitVec.ofNat 64 (trialN w) ∧ t.gpr .x1 = 0 ∧
        t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true ∧ t.mem = s.mem) ∧ Keep mmRegs s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aTab .x9 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h9, m₂, _⟩, k₂⟩ => ?_
  refine WP.mono (trialInit_ok s₂ ((k₂.gpr .x12 (by decide)).trans h12) h.w2)
    fun t ⟨⟨a, b, c, d, e⟩, k₃⟩ => ?_
  exact ⟨⟨by rw [k₃.gpr .x9 (by decide), h9, Nat.mul_zero, Nat.add_zero], a, b, c, d, by rw [e, m₂, m₁]⟩,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

theorem sieve_eq : sieve = ([
    .block (ws ++ base aTab .x9 ++ [movi .x3 128, movi .x4 256, movi .x5 17, .subs .x .x6 .x12 .x5,
      .csel .x .x10 .x4 .x3, movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1]),
    .loop (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)))) (.nonzero .x .x10),
    .block [ldh .x5 fBad, .logic .orr .x .x5 .x5 .x1, sth .x5 fBad]] : List (Prog isa)) := rfl

/-- `sieve`: the mask of an entry of the table's first `4 (trialN w)`
dividing `aN` or'ed into `fBad`. -/
theorem sieve_ok {s : State} {p : PP} {w c : Nat} {v : BitVec 64} (h : PSt p w s)
    (hT : slot w aTab + 2048 ≤ p.Z) (htab : TabOk s.mem p.B w) (hc : wv s.mem p.B (slot w aN) w = c)
    (hv : word s.mem p.B (8 * fBad) = v) :
    WP isa (seqs sieve) s fun t =>
      PSt p w t ∧ word t.mem p.B (8 * fBad) = v ||| mask (anyPre c (4 * trialN w)) ∧
        Frm p.B [(8 * fBad, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have h256 := hws.h256
  rw [sieve_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (sieveInit_ok hws) fun s₁ ⟨⟨h9₁, h10₁, h1₁, h7₁, h8₁, hm₁⟩, k₁⟩ => ?_)
  have hws₁ : Ws s₁ p.B p.Z w := hws.congr' (rs := []) (by rw [hm₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
  have htab₁ : ∀ i < 256, word s₁.mem p.B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i) := fun i hi => by
    rw [hm₁]; exact htab i hi
  have hc₁ : wv s₁.mem p.B (slot w aN) w = c := by rw [hm₁]; exact hc
  have hN : trialN w ≤ 256 ∧ 1 ≤ trialN w := by unfold trialN; split <;> omega_arith
  refine WP.seq (WP.mono (wp_countdown (N := trialN w) (by omega_arith) (by omega_arith) (fun k t => TLInv s₁ p.B p.Z w t ∧
      t.gpr .x9 = off p.B (slot w aTab + 8 * k) ∧ t.gpr .x1 = mask (anyPre c (4 * k)))
    (fun k hk t ⟨hI, h9, hf⟩ _ => tlIter_ok hc₁ hT (by omega_arith) htab₁ hI h9 hf)
    ⟨⟨hws₁, h7₁, h8₁, rfl, Keep.refl _ _⟩, h9₁, by rw [h1₁, Nat.mul_zero, anyPre_zero]; rfl⟩ h10₁)
    fun s₄ ⟨hI₄, _, h1₄⟩ => ?_)
  have hm₄ : s₄.mem = s.mem := hI₄.mem.trans hm₁
  have hv₄ : s₄.mem.readW (off p.B (8 * fBad)) 64 = v := by rw [hm₄]; exact hv
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.mem = s₄.mem.writeW (off p.B (8 * fBad))
      (v ||| mask (anyPre c (4 * trialN w))))
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
