module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawRound

import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeInput
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
/-! # The complete native primality operation matches DSA's specification -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/PrimeReject.lean`, which only this module imported.
section

/-! Small-prime rejection returns composite without consuming witness bytes. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem primeReject_ok {P : PrimeParams} {used : Nat} {s : State} (h : PrimeInput P used s) :
    WP isa (.block [movi .x3 3, sth .x3 kStat]) s fun t =>
      PrimeInput P used t ∧ word t.mem P.B (8 * kStat) = BitVec.ofNat 64 3 ∧
      Frm P.B [(8 * kStat, 8)] s.mem t.mem ∧ Keep [.x3] s t := by
  have h256 := h.ws.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = s.mem.writeW (off P.B (8 * kStat)) (BitVec.ofNat 64 3))
    (by
      brun [h.ws.x0, hdr_enc (show kStat < 32 by decide),
        h.ws.scr.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega)]
      rfl) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have hf : Frm P.B [(8 * kStat, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ P.B _ (by decide)) (by simp)
  have ht := h.ws.congr' hf (by intro r hr; rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide)) hk (by decide)
  have hn : wv t.mem P.B (slot P.w aN) P.w = P.N := by
    rw [hf.wv_eq (by intro r hr; rw [List.mem_singleton.mp hr]; right; simp only [slot, hdrBytes, aN, kStat, sFn]; omega_arith)
      (by have := h.ws.scr.nowrap; have := h.ws.sl (show aN < 16 by decide); omega)]
    exact h.n
  have hi := h.advance ht hn hf (hk.mono (by decide))
    (by intro r hr; rw [List.mem_singleton.mp hr]; change 256 ≤ P.Z; exact P.z256)
    (by
      intro j hj r hr; rw [List.mem_singleton.mp hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact ⟨hi, by rw [hm, word_writeW_self], hf, hk⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/PrimeLoop.lean`, which only this module imported.
section

/-! # The complete DSA witness loop implements RSA's blinded primality loop -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MillerRabin.AArch64

theorem millerRabin_ok (M : Mont) (K : Kernel) {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeState P used s) (hu : used ≤ P.rand.length) :
    WP isa (Impl.Dsa.AArch64.Generation.millerRabin M.mm K.run P.len P.drawBytes) s
      (PrimeLoopEnd P s (primeRest P 1 0 used)) := by
  unfold Impl.Dsa.AArch64.Generation.millerRabin
  refine WP.seq (WP.mono (primeLoopInit_ok h hu) fun u hI => ?_)
  exact WP.loop
    (fun n t => ∃ i uni used', n = P.rand.length - used' ∧
      PrimeLoopState P s (primeRest P 1 0 used) i uni used' t)
    (fun n t ⟨i, uni, used', hn, hstate⟩ =>
      WP.mono (primeIteration_ok M K hstate) fun t' ht => ht.imp (fun ht => ht)
        fun ⟨he, uni', hnext⟩ =>
          ⟨he, P.rand.length - (used' + P.drawBytes),
            by have := hnext.usedBound; have := P.drawMin; omega,
            i + 1, uni', used' + P.drawBytes, rfl, hnext⟩)
    (P.rand.length - used) u ⟨1, 0, used, rfl, hI⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.MillerRabin.AArch64

def primeRanges (w : Nat) : List (Nat × Nat) :=
  primeTrialRanges w ++ modulusRanges w ++ drawRoundRanges w ++ [(8 * kStat, 8)]

def PrimeEnd (P : PrimeParams) (s₀ : State) (res : Option (Bool × List Byte)) (s : State) : Prop :=
  ∃ used, PrimeInput P used s ∧ used ≤ P.rand.length ∧
    (res = none → word s.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, res = some (b, rest) →
      word s.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      used = P.rand.length - rest.length) ∧
    WorkFrame P.B (primeRanges P.w) (primeExtras P) s₀.mem s.mem ∧ Keep mmRegs s₀ s

theorem probablePrime_ok (M : Mont) (K : Kernel) {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeInput P used s) (hu : used ≤ P.rand.length)
    (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z) (hn : 8161 < P.N)
    (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w)
    (hchecks : P.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength P.N)) :
    WP isa (Impl.Dsa.AArch64.Generation.probablePrime M.mm K.run P.len P.drawBytes) s
      (PrimeEnd P s (Spec.Dsa.probablePrime P.N (P.rand.drop used))) := by
  have hspec := VG.Proof.Dsa.Generation.probablePrime_large (by omega : 3 < P.N) P.odd (P.rand.drop used)
  unfold Impl.Dsa.AArch64.Generation.probablePrime
  refine WP.seq (WP.mono (primeTrial_ok h hw hz hn hpolicy) fun u ⟨hflag, hi, hf, hk⟩ => ?_)
  have fu : WorkFrame P.B (primeRanges P.w) (primeExtras P) s.mem u.mem :=
    hf.work.mono (by intro r hr; simp only [primeRanges, List.mem_append]; exact Or.inl (Or.inl (Or.inl hr)))
  refine WP.ite (!Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength P.N) P.N)
    hflag (fun hpass => ?_) (fun hfail => ?_)
  · have hnot : Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength P.N) P.N = false := by
      simpa only [Bool.not_eq_true'] using hpass
    have hres : Spec.Dsa.probablePrime P.N (P.rand.drop used) = primeRest P 1 0 used := by
      rw [hspec, hnot]
      simp only [Bool.false_eq_true, ite_false, primeRest, hchecks]
    refine WP.seq (WP.mono (primeInputSetup_ok M hi hw) fun v ⟨hv, fv, kv⟩ => ?_)
    have fuv : WorkFrame P.B (primeRanges P.w) (primeExtras P) u.mem v.mem :=
      fv.work.mono (by intro r hr; simp only [primeRanges, List.mem_append]; exact Or.inl (Or.inl (Or.inr hr)))
    refine WP.mono (millerRabin_ok M K hv hu) fun t ⟨used', ht, hut, he, hr, ft, kt⟩ => ?_
    refine ⟨used', ht.input, hut, ?_, ?_, ?_, ((hk.trans kv).trans kt).mono (by decide)⟩
    · intro hnone; exact he (hres ▸ hnone)
    · intro b rest hs; exact hr b rest (hres ▸ hs)
    · exact (fu.trans fuv).trans (ft.mono (by
        intro r hr; simp only [primeRanges, List.mem_append]; exact Or.inl (Or.inr hr)))
  · have hyes : Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength P.N) P.N = true := by
      simpa only [Bool.not_eq_false'] using hfail
    have hres : Spec.Dsa.probablePrime P.N (P.rand.drop used) = some (false, P.rand.drop used) := by
      rw [hspec, hyes]; rfl
    refine WP.mono (primeReject_ok hi) fun t ⟨ht, hstat, ft, kt⟩ => ?_
    refine ⟨used, ht, hu, ?_, ?_, ?_, (hk.trans kt).mono (by decide)⟩
    · intro hnone; rw [hres] at hnone; cases hnone
    · intro b rest hs
      obtain ⟨hb, hr⟩ := Prod.mk.inj (Option.some.inj (hres.symm.trans hs))
      subst b rest
      exact ⟨hstat, by rw [List.length_drop]; omega⟩
    · exact fu.trans (ft.work.mono (by
        intro r hr; simp only [primeRanges, List.mem_append]; exact Or.inr hr))

end VG.Proof.Dsa.AArch64.Generation
