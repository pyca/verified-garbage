module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopState

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopExhausted
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
import Mathlib.Tactic.Conv
/-! # One guarded iteration of DSA's finite primality loop -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/LoopRound.lean`, which only this module imported.
section

/-! # Continue or finish the primality loop after one complete draw -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64
open VG.Proof.MillerRabin.X86_64

theorem loopRound_ok (M : Mont) (K : Kernel) {P : PrimeParams} {mi : BitVec 64} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat}
    (h : PrimeLoopState P mi s₀ res i uni used s) (hroom : used + P.drawBytes ≤ P.rand.length) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)
      (.block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)])) s fun t =>
        (isa.eval .e t = some false ∧ PrimeLoopEnd P mi s₀ res t) ∨
        (isa.eval .e t = some true ∧ ∃ uni', PrimeLoopState P mi s₀ res (i + 1) uni' (used + P.drawBytes) t) := by
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
  refine WP.mono (statCmp_ok hu.ready.good P.dims.z (by split <;> (try split) <;> decide) hstat)
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
      refine Or.inr ⟨by simp [eval, hz, hgo], uni + wt.2.toNat, ht,
        by rw [hm]; exact hki, by rw [hm]; exact hkuni, hroom, by omega, hbound,
        by have := h.uniformBound; omega, ?_, hres.symm, hf, hk⟩
      change i + 1 ≤ 16 ∨ uni + wt.2.toNat < P.checks
      omega
    · have hnot : ¬ (i + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨ uni + wt.2.toNat < P.checks) := by
        change ¬ (i + 1 ≤ 16 ∨ uni + wt.2.toNat < P.checks); omega
      have hdone := VG.Proof.RsaKeyGen.mrLoop_done P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1
        (Spec.Rsa.splitTwos (P.N - 1)).2 (P.rand.drop (used + P.drawBytes)) (i + 1) (uni + wt.2.toNat) hnot
      change primeRest P (i + 1) (uni + wt.2.toNat) (used + P.drawBytes) = _ at hdone
      refine Or.inl ⟨by simp [eval, hz, hgo], primeLoopEnd_some ht hroom (hres.trans hdone) ?_ hf hk⟩
      simpa [hgo] using hstat'
  · rw [ite_eq_right hpass] at hres hstat' hz
    exact Or.inl ⟨by simp [eval, hz], primeLoopEnd_some ht hroom hres hstat' hf hk⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64

theorem primeIteration_ok (M : Mont) (K : Kernel) {P : PrimeParams} {mi : BitVec 64} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat}
    (h : PrimeLoopState P mi s₀ res i uni used s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeIteration
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)) s fun t =>
        (isa.eval .e t = some false ∧ PrimeLoopEnd P mi s₀ res t) ∨
        (isa.eval .e t = some true ∧ ∃ uni', PrimeLoopState P mi s₀ res (i + 1) uni' (used + P.drawBytes) t) := by
  unfold Impl.Dsa.X86_64.Generation.primeIteration
  simp only [seqs]
  refine WP.seq (WP.mono (tapeCheck_ok h.state h.usedBound) fun u ⟨hcf, hm, ku⟩ => ?_)
  have hu := h.of_mem hm (ku.mono (by decide))
  refine WP.seq (WP.ite (decide (P.rand.length < used + P.drawBytes)) (by simp [eval, hcf])
    (fun hshort => ?_) (fun hroom => ?_))
  · exact WP.seq_iff.mp (WP.mono (loopExhausted_ok hu (by simpa only [decide_eq_true_eq] using hshort))
      fun _ ht => Or.inl ht)
  · exact WP.seq_iff.mp (loopRound_ok M K hu (by simpa only [decide_eq_false_iff_not, Nat.not_lt] using hroom))

end VG.Proof.Dsa.X86_64.Generation
