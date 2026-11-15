module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ProbablePrime
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Trial division to the first divisor leaks the same in runs with the same candidate:
RSA's timing proof of a word of the table, and a count of words that the candidate gives. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem nativeTrialHead_ok {q : VG.Proof.RsaKeyGen.AArch64.FPub} {s : State} (hw : VG.Proof.Rsa.AArch64.Ws s q.B q.Z q.w)
    (hT : slot q.w aTab + 2048 ≤ q.Z) :
    WP isa (.block (ws ++ base aTab .x9 ++ tabWrite ++ [movi .x3 128, movi .x4 256, movi .x5 17,
      .subs .x .x6 .x12 .x5, .csel .x .x10 .x4 .x3, movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1])) s fun t =>
      (0 < trN q ∧ TI q 0 t) ∧ wv t.mem q.B (slot q.w aN) q.w = wv s.mem q.B (slot q.w aN) q.w := by
  have hn := hw.scr.nowrap
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨⟨h12₁, h11₁, hm₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aTab .x9 ((k₁.gpr .x0 (by decide)).trans hw.x0) h11₁)
    fun s₂ ⟨⟨h9₂, hm₂, _⟩, k₂⟩ => ?_
  refine WP.mono (tabWrites_ok (hw.scr.congr (k₁.trans k₂).wr) hT h9₂ 256 (Nat.le_refl _))
    fun s₃ ⟨htab₃, ho₃, k₃⟩ => ?_
  rw [hm₂, hm₁] at ho₃
  have h12₃ : s₃.gpr .x12 = BitVec.ofNat 64 q.w :=
    (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12₁)
  refine WP.mono (trialInit_ok s₃ h12₃ hw.w2) fun s₄ ⟨⟨h10₄, h1₄, h7₄, h8₄, hm₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hf₄ : Frm q.B [(slot q.w aTab, 2048)] s.mem s₄.mem := by rw [hm₄]; exact Frm.of_outside ho₃ (by simp)
  have hTa : slot q.w aN + 8 * q.w ≤ slot q.w aTab := by unfold slot aN aTab; omega
  refine ⟨?_, by rw [hm₄, ho₃.wv (Or.inl hTa) (by omega_using [hT, hn, hTa])]⟩
  refine ⟨(trN_le q).2, hw.congr' hf₄ (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k14
    (by decide), hT, by rw [k₄.gpr .x9 (by decide), k₃.gpr .x9 (by decide), h9₂, Nat.mul_zero, Nat.add_zero],
    by rw [h10₄, Nat.sub_zero]; rfl, h7₄, h8₄, fun i hi => by rw [hm₄]; exact htab₃ i hi,
    by rw [h1₄, Nat.mul_zero, anyPre_zero]; rfl⟩

/-- The public data of DSA's trial division: the workspace, and the candidate. -/
abbrev EPub := VG.Proof.RsaKeyGen.AArch64.FPub × Nat

/-- The words of the table the loop runs for the candidate. -/
abbrev earlyN (q : EPub) : Nat := earlyWords q.2 (trN q.1)

/-- Before word `k` of the table. -/
def EI (q : EPub) (k : Nat) (s : State) : Prop :=
  TI q.1 k s ∧ wv s.mem q.1.B (slot q.1.w aN) q.1.w = q.2

/-- One word of the table, and whether the loop runs another. -/
theorem earlyTrialIter_ok {q : EPub} {k : Nat} {s : State} (hk : k < earlyN q) (h : EI q k s) :
    WP isa (seqs (trialWord ++
      ([.block [.logic .eor .x .x3 .x1 .x8, .logic .and .x .x10 .x10 .x3]] : List (Prog isa)))) s fun t =>
      isa.eval (.nonzero .x .x10) t = some (decide (k + 1 < earlyN q)) ∧ (k + 1 < earlyN q → EI q (k + 1) t) ∧
        (k + 1 = earlyN q → True) := by
  obtain ⟨⟨hw, hT, h9, h10, h7, h8, htab, h1⟩, hc⟩ := h
  have hN := trN_le q.1
  have hkT : k < trN q.1 := Nat.lt_of_lt_of_le hk (earlyWords_le _ _)
  rw [hc] at h1
  refine WP.mono (earlyIter_ok (s₀ := s) hc hT hkT hN.1 htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩ h9 h1 h10)
    fun t ⟨hI, h9', h1', h10'⟩ => ⟨?_, fun hk' => ⟨⟨hI.ws, hT, h9', ?_, hI.x7, hI.x8, fun i hi => by
      rw [hI.mem]; exact htab i hi, by rw [h1', hI.mem, hc]⟩, by rw [hI.mem]; exact hc⟩, fun _ => trivial⟩
  · rw [eval_nonzero, h10']
    exact congrArg some (early_cond hk hN.1)
  · rw [h10', (lt_earlyWords.mp hk').2]; rfl

/-- One word of the table leaks the same. -/
theorem earlyTrialBody_ct : RelCT isa (Two fun (p : EPub × Nat) s => p.2 < earlyN p.1 ∧ EI p.1 p.2 s)
    (seqs (trialWord ++
      ([.block [.logic .eor .x .x3 .x1 .x8, .logic .and .x .x10 .x10 .x3]] : List (Prog isa))))
    fun _ _ => True := by
  refine RelCT.seqs_append trialWord_ne (by simp) (RelCT.seq (two_post (Ψ := fun _ _ => True)
    (two_map (fun p : EPub × Nat => (p.1.1, p.2))
      (fun p s h => ⟨Nat.lt_of_lt_of_le h.1 (earlyWords_le _ _), h.2.1⟩) trialBody_ct)
    (fun p s h => ?_)) (two_taint [] (pins_nil₀ _) (by taint_decide)))
  obtain ⟨hk, ⟨hw, hT, h9, h10, h7, h8, htab, h1⟩, hc⟩ := h
  have hN := trN_le p.1.1
  have hkT : p.2 < trN p.1.1 := Nat.lt_of_lt_of_le hk (earlyWords_le _ _)
  exact WP.mono (tlIter_ok (s₀ := s) rfl hT (by omega_using [hkT, hN])
    htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩ h9 h1) fun _ _ => trivial

/-- Trial division to the first divisor leaks the same in runs with the same
workspace and candidate. It needs the table's actual bound, without RSA
keygen's larger arena. -/
theorem trialEarly_ct :
    RelCT isa (Two fun (q : EPub) s => VG.Proof.Rsa.AArch64.Ws s q.1.B q.1.Z q.1.w ∧
      slot q.1.w aTab + 2048 ≤ q.1.Z ∧ wv s.mem q.1.B (slot q.1.w aN) q.1.w = q.2) (seqs trialEarly)
      (fun _ _ => True) := by
  have hh := fun (q : EPub) s (h : VG.Proof.Rsa.AArch64.Ws s q.1.B q.1.Z q.1.w ∧ slot q.1.w aTab + 2048 ≤ q.1.Z ∧
      wv s.mem q.1.B (slot q.1.w aN) q.1.w = q.2) =>
    WP.mono (nativeTrialHead_ok h.1 h.2.1) fun t ⟨⟨_, hI⟩, hc⟩ =>
      (⟨earlyWords_pos q.2 (trN_le q.1).2, hI, hc.trans h.2.2⟩ : 0 < earlyN q ∧ EI q 0 t)
  simp only [List.append_assoc] at hh
  simp only [trialEarly, seqs, List.append_assoc]
  refine RelCT.seq (two_post (ws_block_ct0 (fun q : EPub => q.1.B) (fun q => q.1.Z) (fun q => q.1.w)
      (fun _ _ h => h.1) (by taint_decide)) hh)
    ((two_loop (Φ := EI) (Ψ := fun _ _ => True) earlyN earlyTrialBody_ct fun _ _ _ hk h => earlyTrialIter_ok hk h).mono
      (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.Dsa.AArch64.Generation
