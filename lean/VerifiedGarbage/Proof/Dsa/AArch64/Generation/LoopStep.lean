module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTapeCheck
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Dsa.AArch64.Generation.LoopExhausted`, which this module and modules that import it used -/

section

/-! Exhaustion terminates the primality loop before reading an incomplete draw. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem loopExhausted_ok {P : PrimeParams} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat}
    (h : PrimeLoopState P s₀ res i uni used s) (hshort : P.rand.length < used + P.drawBytes) :
    WP isa (.seq (.block [movi .x3 0, sth .x3 kStat])
      (.block [ldh .x3 kStat, .subImm .x .x3 .x3 4])) s fun t =>
        isa.eval (.zero .x .x3) t = some false ∧ PrimeLoopEnd P s₀ res t := by
  have hr := VG.Proof.RsaKeyGen.mrLoop_step P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1
    (Spec.Rsa.splitTwos (P.N - 1)).2 P.drawBytes P.rand i uni used h.go P.drawWidth (by have := P.drawMin; omega_using [this])
  have hnone : res = none := by
    rw [← h.rest]
    change Spec.RsaKeyGen.loop _ _ _ = _
    rw [hr, ite_eq_right (by omega_using [hshort])]
  have h256 := h.state.ready.ws.h256
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun u =>
      u.mem = s.mem.writeW (off P.B (8 * kStat)) (BitVec.ofNat 64 0)) (by
      brun [h.state.ready.ws.x0, hdr_enc (show kStat < 32 by decide),
        h.state.ready.ws.scr.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega_using [h256])]
      rfl) rfl rfl rfl) fun u ⟨hm, ku⟩ => ?_)
  have hf : Frm P.B [(8 * kStat, 8)] s.mem u.mem := by
    rw [hm]
    exact Frm.of_outside (writeW_outside _ P.B _ (d := 8 * kStat) (by decide)) (by simp)
  have k : Keep mmRegs s u := ku.mono (by decide)
  have hready := (h.state.ready.write_header (BitVec.ofNat 64 0) P.exponentRoom (i := kStat) (by decide)).of_words
    P.exponentRoom (fun _ _ => by change word u.mem _ _ = _; rw [hm]) ku.wr
      ((ku.gpr .x0 (by decide)).trans h.state.ready.ws.x0)
  have hused : word u.mem P.B (8 * kUsed) = BitVec.ofNat 64 used :=
    (hf.word_eq (by intro r hr; rw [List.mem_singleton.mp hr]; decide) (by decide)).trans h.state.used
  have hu := h.state.advance hready hused hf.work k
    (by intro r hr; rw [List.mem_singleton.mp hr]; change 256 ≤ P.Z; exact P.z256)
    (by
      intro j hj r hr; rw [List.mem_singleton.mp hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hz : word u.mem P.B (8 * kStat) = BitVec.ofNat 64 0 := by rw [hm, word_writeW_self]
  have hend : PrimeLoopEnd P s₀ res u := by
    refine ⟨used, hu, h.usedBound, fun _ => hz, ?_, ?_, (h.keep.trans k).mono (by decide)⟩
    · intro b rest he; rw [hnone] at he; cases he
    · exact h.frame.trans (hf.work.mono (by simp [drawRoundRanges, sampleRoundRanges]))
  refine WP.mono (statCmp_ok hu.ready.ws (v := 0) (by decide) hz) fun t ⟨hzt, hmt, kt⟩ => ?_
  exact ⟨by simpa using hzt, hend.of_mem hmt (kt.mono (by decide))⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.LoopRound`, which only this module used -/

section

/-! # Continue or finish the primality loop after one complete draw -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64

theorem loopRound_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {P : PrimeParams} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat}
    (h : PrimeLoopState P s₀ res i uni used s) (hroom : used + P.drawBytes ≤ P.rand.length) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run P.len P.drawBytes)
      (.block [ldh .x3 kStat, .subImm .x .x3 .x3 4])) s fun t =>
        (isa.eval (.zero .x .x3) t = some false ∧ PrimeLoopEnd P s₀ res t) ∨
        (isa.eval (.zero .x .x3) t = some true ∧ ∃ uni', PrimeLoopState P s₀ res (i + 1) uni' (used + P.drawBytes) t) := by
  let wt := Spec.RsaKeyGen.witness (P.N - 1) (Spec.Rsa.os2ip ((P.rand.drop used).take P.drawBytes))
  have hr := VG.Proof.RsaKeyGen.mrLoop_step P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1
    (Spec.Rsa.splitTwos (P.N - 1)).2 P.drawBytes P.rand i uni used h.go P.drawWidth (by have := P.drawMin; omega_using [this])
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
        conv_lhs => rw [show i = (i - 1) + 1 by have := h.i1; omega_using [this], Nat.mul_add, Nat.mul_one]
        exact Nat.add_le_add_right h.countBound _
      have hb : wt.2.toNat ≤ 1 := by cases wt.2 <;> decide
      refine Or.inr ⟨by simpa [hgo] using hz, uni + wt.2.toNat, ht,
        by rw [hm]; exact hki, by rw [hm]; exact hkuni, hroom, by omega_using [], hbound,
        by have := h.uniformBound; omega_using [hb, this], ?_, hres.symm, hf, hk⟩
      change i + 1 ≤ 16 ∨ uni + wt.2.toNat < P.checks
      omega_using [hgo]
    · have hnot : ¬ (i + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨ uni + wt.2.toNat < P.checks) := by
        change ¬ (i + 1 ≤ 16 ∨ uni + wt.2.toNat < P.checks); omega_using [hgo]
      have hdone := VG.Proof.RsaKeyGen.mrLoop_done P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1
        (Spec.Rsa.splitTwos (P.N - 1)).2 (P.rand.drop (used + P.drawBytes)) (i + 1) (uni + wt.2.toNat) hnot
      change primeRest P (i + 1) (uni + wt.2.toNat) (used + P.drawBytes) = _ at hdone
      refine Or.inl ⟨by simpa [hgo] using hz, primeLoopEnd_some ht hroom (hres.trans hdone) ?_ hf hk⟩
      simpa [hgo] using hstat'
  · rw [ite_eq_right hpass] at hres hstat' hz
    exact Or.inl ⟨by simpa using hz, primeLoopEnd_some ht hroom hres hstat' hf hk⟩

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # One guarded iteration of DSA's finite primality loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MillerRabin.AArch64

theorem primeIteration_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {P : PrimeParams} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat}
    (h : PrimeLoopState P s₀ res i uni used s) :
    WP isa (Impl.Dsa.AArch64.Generation.primeIteration
      (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run P.len P.drawBytes)) s fun t =>
        (isa.eval (.zero .x .x3) t = some false ∧ PrimeLoopEnd P s₀ res t) ∨
        (isa.eval (.zero .x .x3) t = some true ∧ ∃ uni', PrimeLoopState P s₀ res (i + 1) uni' (used + P.drawBytes) t) := by
  unfold Impl.Dsa.AArch64.Generation.primeIteration
  simp only [seqs]
  refine WP.seq (WP.mono (tapeCheck_ok h.state h.usedBound) fun u ⟨hcf, hm, ku⟩ => ?_)
  have hu := h.of_mem hm (ku.mono (by decide))
  refine WP.seq (WP.ite (decide (P.rand.length < used + P.drawBytes)) hcf
    (fun hshort => ?_) (fun hroom => ?_))
  · exact WP.seq_iff.mp (WP.mono (loopExhausted_ok hu (by simpa only [decide_eq_true_eq] using hshort))
      fun _ ht => Or.inl ht)
  · exact WP.seq_iff.mp (loopRound_ok M K hu (by simpa only [decide_eq_false_iff_not, Nat.not_lt] using hroom))

end VG.Proof.Dsa.AArch64.Generation
