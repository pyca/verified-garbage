module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Front1
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint1
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint4
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: `p ≥ q`, `p − 1` and `q − 1` (`primes_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32)
open VG.Proof.Rsa (b2n)

theorem ite_b2n {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if b2n (decide p) = 0 then a else b) = if p then b else a := by
  by_cases h : p <;> simp [h, b2n]

theorem b2n_le' (x : Bool) : b2n x ≤ 1 := by cases x <;> decide

/-- The arrays after the primes. -/
def A1 (P : KP) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (A0 P σ) aP (pv P σ)) aQ (qv P σ)) aPm (pm P σ)) aQm (qm P σ)

abbrev L1 : List Nat := aQm :: aPm :: aQ :: aP :: L0

abbrev S1 (P : KP) (E : State → Prop) : State → State → Prop := St P E (A1 P) L1 (fun _ _ => 0) []

section
variable {P : KP}

theorem sub32_one' {W x : Nat} (hx : x < 2 ^ (32 * W)) :
    (if x < 1 then 0 else sub32 W x 1) = x - 1 := by
  split
  · omega
  · exact sub32_le (by omega) hx

theorem primes_vp {E : State → Prop} : VP (S0 P E) primes (S1 P E) := by
  simp only [primes, List.cons_append, List.nil_append, List.append_assoc]
  refine VP.assoc (VP.seq (St.pltS ltPQ_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine VP.seq (St.psel selP_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by simp only [upd_self]; exact b2n_le' _) ?_
  refine VP.seq (St.psel selQ_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by simp only [upd_self]; exact b2n_le' _) ?_
  refine VP.assoc (VP.seq (St.pltS ltP1_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine VP.seq (St.psel selPm_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by simp only [upd_self]; exact b2n_le' _) ?_
  refine VP.assoc (VP.seq (St.pltS ltQ1_taint (by simp) (by simp) (by decide) (by decide) (by decide)) ?_)
  refine (St.psel selQm_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    fun _ _ => by simp only [upd_self]; exact b2n_le' _).mono (fun _ _ h => h) fun σ s h =>
      h.mono (fun j hj => ⟨by mem_sub, ?_⟩) (fun d _ => absurd ‹d ∈ []› (by simp))
  have pv' := pv_lt P σ; have qv' := qv_lt P σ
  have p8 : 2 ^ (8 * P.K) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by simp only [KP.W]; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [A1, A0, Aload, upd, ↓reduceIte, ite_b2n]
  · exact sub32_one' (show qv P σ < _ by omega)
  · exact sub32_one' (show pv P σ < _ by omega)
  · rfl
  · rfl

end

end VG.Proof.RsaKeyGen.Arm.Key
