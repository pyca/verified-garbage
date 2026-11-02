module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopState

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import Mathlib.Tactic.Conv

/-! # Continue or finish the primality loop after one complete draw -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64

theorem loopRound_ok (M : Mont) (K : Kernel) {P : PrimeParams} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat}
    (h : PrimeLoopState P s₀ res i uni used s) (hroom : used + P.drawBytes ≤ P.rand.length) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run P.len P.drawBytes)
      (.block [ldh .x3 kStat, .subImm .x .x3 .x3 4])) s fun t =>
        (isa.eval (.zero .x .x3) t = some false ∧ PrimeLoopEnd P s₀ res t) ∨
        (isa.eval (.zero .x .x3) t = some true ∧ ∃ uni', PrimeLoopState P s₀ res (i + 1) uni' (used + P.drawBytes) t) := by
  let wt := Spec.RsaKeyGen.witness (P.N - 1) (Spec.Rsa.os2ip ((P.rand.drop used).take P.drawBytes))
  have hr := VG.Proof.RsaKeyGen.mrLoop_step P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1
    (Spec.Rsa.splitTwos (P.N - 1)).2 P.drawBytes P.rand i uni used h.go P.drawWidth (by have := P.drawMin; omega)
  have hut : (if wt.2 then 1 else 0) = wt.2.toNat := by cases wt.2 <;> rfl
  change primeRest P i uni used = if used + P.drawBytes ≤ P.rand.length then
    if Proof.MillerRabin.Round.round P.N wt.1 then primeRest P (i + 1) (uni + if wt.2 then 1 else 0) (used + P.drawBytes)
    else some (false, P.rand.drop (used + P.drawBytes)) else none at hr
  rw [ite_eq_left hroom, hut] at hr
  have hres := h.rest.symm.trans hr
  refine WP.seq (WP.mono (drawRound_ok M K h.state hroom h.ki h.kuni h.counter_bound.1 h.counter_bound.2)
    fun u ⟨hu, hstat, hcount, hfu, ku⟩ => ?_)
  change word u.mem P.B (8 * kStat) = BitVec.ofNat 64
    (if Proof.MillerRabin.Round.round P.N wt.1 then (if i + 1 < 17 ∨ uni + wt.2.toNat < P.checks then 4 else 1) else 3) at hstat
  change (Proof.MillerRabin.Round.round P.N wt.1 = true → word u.mem P.B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
    word u.mem P.B (8 * kUni) = BitVec.ofNat 64 (uni + wt.2.toNat)) at hcount
  refine WP.mono (statCmp_ok hu.ready.ws (by split <;> (try split) <;> decide) hstat)
    fun t ⟨hz, hm, kt⟩ => ?_
  have k : Keep mmRegs u t := kt.mono (by decide)
  have ht := hu.of_mem hm k
  have hf : WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s₀.mem t.mem := by rw [hm]; exact h.frame.trans hfu
  have hk : Keep mmRegs s₀ t := ((h.keep.trans ku).trans k).mono (by decide)
  have hstat' : word t.mem P.B (8 * kStat) = BitVec.ofNat 64
    (if Proof.MillerRabin.Round.round P.N wt.1 then (if i + 1 < 17 ∨ uni + wt.2.toNat < P.checks then 4 else 1) else 3) := by rw [hm]; exact hstat
  by_cases hpass : Proof.MillerRabin.Round.round P.N wt.1 = true
  · rw [ite_eq_left hpass] at hres hstat' hz
    by_cases hgo : i + 1 < 17 ∨ uni + wt.2.toNat < P.checks
    · have hki := (hcount hpass).1
      have hkuni := (hcount hpass).2
      have hbound : P.drawBytes * (i + 1 - 1) ≤ used + P.drawBytes := by
        rw [Nat.add_sub_cancel]
        conv_lhs => rw [show i = (i - 1) + 1 by have := h.i1; omega, Nat.mul_add, Nat.mul_one]
        exact Nat.add_le_add_right h.countBound _
      have hb : wt.2.toNat ≤ 1 := by cases wt.2 <;> decide
      refine Or.inr ⟨by simpa [hgo] using hz, uni + wt.2.toNat, ht,
        by rw [hm]; exact hki, by rw [hm]; exact hkuni, hroom, by omega, hbound,
        by have := h.uniformBound; omega, ?_, hres.symm, hf, hk⟩
      change i + 1 ≤ 16 ∨ uni + wt.2.toNat < P.checks
      omega
    · have hnot : ¬ (i + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨ uni + wt.2.toNat < P.checks) := by
        change ¬ (i + 1 ≤ 16 ∨ uni + wt.2.toNat < P.checks); omega
      have hdone := VG.Proof.RsaKeyGen.mrLoop_done P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1
        (Spec.Rsa.splitTwos (P.N - 1)).2 (P.rand.drop (used + P.drawBytes)) (i + 1) (uni + wt.2.toNat) hnot
      change primeRest P (i + 1) (uni + wt.2.toNat) (used + P.drawBytes) = _ at hdone
      refine Or.inl ⟨by simpa [hgo] using hz, primeLoopEnd_some ht hroom (hres.trans hdone) ?_ hf hk⟩
      simpa [hgo] using hstat'
  · rw [ite_eq_right hpass] at hres hstat' hz
    exact Or.inl ⟨by simpa using hz, primeLoopEnd_some ht hroom hres hstat' hf hk⟩

end VG.Proof.Dsa.AArch64.Generation
