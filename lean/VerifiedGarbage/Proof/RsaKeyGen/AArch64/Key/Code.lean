import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Res
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Main
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Entry
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

/-!
# An RSA key from its primes on AArch64: correctness

`code`, from a state `keyA` allows, ends as `keyOp` (`keyCode_wp`,
`keyCode_correct`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

theorem code_eq : code = seqs (([.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)] : List (Prog isa)) ++
    ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ (([.block [sth .x3 kEv]] : List (Prog isa)) ++
      (order ++ (decTo aPm aPa ++ decTo aQm aQa)))))) ++
    ((lcmPart ++ ([dPart] ++ smallMask)) ++ ([.ite (.nonzero .x .x15) (zeros 2) keyPart] : List (Prog isa))))) := by
  simp only [code, List.append_assoc]

/-- The postcondition, from the results against `keyOp`. -/
theorem keyPost_of {s t : State} (c : KCtx s) (R : OutsRes (keyIn s) t.mem (t.gpr .x0)) : keyPost s t := by
  have ho : keyOuts s = outsL (keyIn s) := by simp only [keyOuts, outsL, keyIn, c.x1]
  unfold keyPost keyRes
  rw [ho]
  exact R

theorem mask_bne_k (b : Bool) : (mask b != 0) = b := by cases b <;> decide

/-- `code` computes `keyOp`. -/
theorem keyCode_wp (s : State) (h : keyPre s) : WP isa code s fun t => abiPreserved s t ∧ keyPost s t := by
  have c := keyCtx_of h
  rw [code_eq]
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (keyStart_k c) fun t₁ k₁ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [lcmPart, phi, mulTo])
    (WP.mono (front_k k₁ c.L) fun t₂ P => ?_)
  refine wp_seqs_append (by simp [lcmPart, phi, mulTo]) (by simp) (WP.mono (front2_k P.1 c.L) fun t₃ F => ?_)
  obtain ⟨ok, hok, hiff, hx15⟩ := F.x15
  obtain ⟨ok', hok', -, hdd⟩ := F.d
  have hoo : ok' = ok := by
    rw [hok] at hok'
    cases ok <;> cases ok' <;> first | rfl | exact absurd hok' (by decide)
  subst hoo
  refine WP.ite (decide (av (keyIn s) t₃.mem aDd ≤ 2 ^ (8 * (keyIn s).pl)) && ok')
    (by rw [VG.Proof.MlKem.AArch64.eval_nonzero, hx15, mask_bne_k]) (fun hb => ?_) (fun hb => ?_)
  · -- `d ≤ 2^(8 pl)`: zeros, the status 2.
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨d, hd⟩ := hiff.mpr hb.2
    have hsm := hdd d hd ▸ hb.1
    exact WP.mono (zerosPart_k F.ks c.L c.O) fun t Z =>
      ⟨abiPreserved_of_keep ((F.ks.keep.trans Z.2.2.2).mono (by decide)), keyPost_of c (outsRes_zeros hd hsm Z)⟩
  · refine WP.mono (keyPart_k F c.L c.O hok) fun t T => ?_
    have R := outsRes_tail c.L hiff hdd hb T
    obtain ⟨_, _, _, _, _, kt⟩ := T
    exact ⟨abiPreserved_of_keep ((F.ks.keep.trans kt).mono (by decide)), keyPost_of c R⟩

/-- `vg_rsa_keygen_key`. -/
theorem keyCode_correct (s : State) (h : keyA.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ keyA.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := keyCode_wp s h
  exact ⟨t, s', he, hg, hp⟩

end VG.Proof.RsaKeyGen.AArch64.Key
