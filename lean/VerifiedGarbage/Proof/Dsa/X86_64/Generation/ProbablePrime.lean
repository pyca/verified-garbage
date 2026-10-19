module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTrial
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeReject
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Framework.Omega

/-! # The complete native primality operation matches DSA's specification -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.MillerRabin.X86_64

def primeRanges (w : Nat) : List (Nat × Nat) :=
  primeTrialRanges w ++ modulusRanges w ++ drawRoundRanges w ++ [(8 * kStat, 8)]

def PrimeEnd (P : PrimeParams) (s₀ : State) (res : Option (Bool × List Byte)) (s : State) : Prop :=
  ∃ mi used, PrimeInput P mi used s ∧ used ≤ P.rand.length ∧
    (res = none → word s.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, res = some (b, rest) →
      word s.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      used = P.rand.length - rest.length) ∧
    WorkFrame P.B (primeRanges P.w) (primeExtras P) s₀.mem s.mem ∧ Keep mmRegs s₀ s

theorem probablePrime_ok (M : Mont) (K : Kernel) {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeInput P mi used s) (hu : used ≤ P.rand.length)
    (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z) (hn : 8161 < P.N)
    (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w)
    (hchecks : P.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength P.N)) :
    WP isa (Impl.Dsa.X86_64.Generation.probablePrime M.mm K.run P.len P.drawBytes) s
      (PrimeEnd P s (Spec.Dsa.probablePrime P.N (P.rand.drop used))) := by
  have hspec := VG.Proof.Dsa.Generation.probablePrime_large (by omega : 3 < P.N) P.odd (P.rand.drop used)
  unfold Impl.Dsa.X86_64.Generation.probablePrime
  refine WP.seq (WP.mono (primeTrial_ok h hw hz hn hpolicy) fun u ⟨hflag, hi, hf, hk⟩ => ?_)
  have fu : WorkFrame P.B (primeRanges P.w) (primeExtras P) s.mem u.mem :=
    hf.work.mono (by intro r hr; simp only [primeRanges, List.mem_append]; exact Or.inl (Or.inl (Or.inl hr)))
  refine WP.ite (!Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength P.N) P.N)
    (by simp [eval, hflag]) (fun hpass => ?_) (fun hfail => ?_)
  · have hnot : Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength P.N) P.N = false := by
      simpa only [Bool.not_eq_true'] using hpass
    have hres : Spec.Dsa.probablePrime P.N (P.rand.drop used) = primeRest P 1 0 used := by
      rw [hspec, hnot]
      simp only [Bool.false_eq_true, ite_false, primeRest, hchecks]
    refine WP.seq (WP.mono (primeInputSetup_ok M hi hw) fun v ⟨mi', hv, fv, kv⟩ => ?_)
    have fuv : WorkFrame P.B (primeRanges P.w) (primeExtras P) u.mem v.mem :=
      fv.work.mono (by intro r hr; simp only [primeRanges, List.mem_append]; exact Or.inl (Or.inl (Or.inr hr)))
    refine WP.mono (millerRabin_ok M K hv hu) fun t ⟨used', ht, hut, he, hr, ft, kt⟩ => ?_
    refine ⟨mi', used', ht.input, hut, ?_, ?_, ?_, ((hk.trans kv).trans kt).mono (by decide)⟩
    · intro hnone; exact he (hres ▸ hnone)
    · intro b rest hs; exact hr b rest (hres ▸ hs)
    · exact (fu.trans fuv).trans (ft.mono (by
        intro r hr; simp only [primeRanges, List.mem_append]; exact Or.inl (Or.inr hr)))
  · have hyes : Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength P.N) P.N = true := by
      simpa only [Bool.not_eq_false'] using hfail
    have hres : Spec.Dsa.probablePrime P.N (P.rand.drop used) = some (false, P.rand.drop used) := by
      rw [hspec, hyes]; rfl
    refine WP.mono (primeReject_ok hi) fun t ⟨ht, hstat, ft, kt⟩ => ?_
    refine ⟨mi, used, ht, hu, ?_, ?_, ?_, (hk.trans kt).mono (by decide)⟩
    · intro hnone; rw [hres] at hnone; cases hnone
    · intro b rest hs
      obtain ⟨hb, hr⟩ := Prod.mk.inj (Option.some.inj (hres.symm.trans hs))
      subst b rest
      exact ⟨hstat, by rw [List.length_drop]; omega⟩
    · exact fu.trans (ft.work.mono (by
        intro r hr; simp only [primeRanges, List.mem_append]; exact Or.inr hr))

end VG.Proof.Dsa.X86_64.Generation
