module

public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Close
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint3
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Inv
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Ops
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads
import VerifiedGarbage.Proof.Rsa.RecoverSubtract
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Loads

/-! # A candidate on ARMv7: `gcd(c − 1, e)` (`gcdCheck_vp`)

From `S2`: `c − 1` and `e` read, the header word `sG := gcd(c − 1, e) = 1`
(`gv`), by `e`'s parity and whether it is 1, which are public, and Z iff it
holds: the stage `S3`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 sub32_of)
open VG.Proof.Rsa (b2n)
open VG.Impl.RsaKeyGen.Arm.Key (isOne)
open VG.Proof.RsaKeyGen.Arm.Key (ivr ivr_spec)

/-- Whether `gcd(c − 1, e) = 1`. -/
def gv (P : CP) (σ : State) : Bool := Nat.gcd (cv P σ - 1) P.e == 1

/-- The arrays after `gcd(c − 1, e)`. -/
def A3 (P : CP) (σ : State) : Nat → Nat := upd (upd (A0 P σ) aCm1 (cv P σ - 1)) aE P.e

abbrev L3 : List Nat := [aE, aCm1, aTwo, aOne, aC, aZero]

def V3 (P : CP) (σ : State) : Nat → Nat := upd (V2 P σ) sG (b2n (gv P σ))

abbrev LS3 : List Nat := [sG, sTr, sCl, sUsed]

abbrev S3 (P : CP) (E : State → Prop) : State → State → Prop := St P E (A3 P) L3 (V3 P) LS3

section
variable {P : CP}

theorem e_lt {σ : State} (pre : In P σ) : P.e < 2 ^ 64 := by
  have := VG.Proof.Rsa.lt_of_os2ip (Spec.Rsa.bytesAt σ.mem (State.addr P.eP) P.el)
  rw [bytesAt_length, pre.eB, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (show 8 * P.el ≤ 64 by have := pre.el2; omega))

theorem gv_even {σ : State} (pre : In P σ) (he : P.e % 2 = 0) : gv P σ = false := by
  unfold gv
  have sh := cv_shape (σ := σ) pre
  have h2 : 2 ∣ Nat.gcd (cv P σ - 1) P.e :=
    Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero (by have := sh.1; omega)) (Nat.dvd_of_mod_eq_zero he)
  have : Nat.gcd (cv P σ - 1) P.e ≠ 1 := fun e => by rw [e] at h2; exact absurd (Nat.le_of_dvd Nat.one_pos h2) (by decide)
  simpa using this

theorem gv_one {σ : State} (he : P.e = 1) : gv P σ = true := by
  unfold gv; rw [he, Nat.gcd_one_right]; rfl

/-- The arrays after `e`'s load. -/
def AE (P : CP) (σ : State) : Nat → Nat :=
  upd (upd (A0 P σ) aCm1 (sub32 P.W (A0 P σ aC) (A0 P σ aOne)))
    aE (Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr P.eP) P.el))

abbrev LE : List Nat := aE :: aCm1 :: L1

/-- The header words after `e`'s flags. -/
def VE (P : CP) (σ : State) : Nat → Nat :=
  upd (upd (V2 P σ) sEo (b2n (decide (AE P σ aE % 2 = 1)))) sE1 (b2n (decide (AE P σ aE = AE P σ aOne)))

abbrev LSE : List Nat := [sE1, sEo, sTr, sCl, sUsed]

theorem AE_e {σ : State} (pre : In P σ) : AE P σ aE = P.e := by
  simp only [AE, upd_self, pre.eB]

theorem AE_one (σ : State) : AE P σ aOne = 1 := by
  simp (config := {decide := true}) only [AE, A0, upd, ↓reduceIte]

theorem AE_zero (σ : State) : AE P σ aZero = 0 := by
  simp (config := {decide := true}) only [AE, A0, upd, ↓reduceIte]

theorem AE_cm1 {σ : State} (pre : In P σ) : AE P σ aCm1 = cv P σ - 1 := by
  obtain ⟨hodd, hlo, hhi⟩ := cv_shape (σ := σ) pre
  have p8 : 2 ^ (8 * P.L) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by simp only [CP.W]; omega)
  have p1 : 1 < 2 ^ (32 * P.W) := Nat.one_lt_two_pow (by have := pre.wge; omega)
  have p2 : 0 < 2 ^ (8 * P.L - 2) := Nat.two_pow_pos _
  simp (config := {decide := true}) only [AE, A0, upd, ↓reduceIte]
  rw [sub32_val (by omega) (by omega), ite_eq_right (by omega)]

theorem VE_o {σ : State} (pre : In P σ) : VE P σ sEo = b2n (decide (P.e % 2 = 1)) := by
  simp (config := {decide := true}) only [VE, upd, ↓reduceIte]; rw [AE_e pre]

theorem VE_1 {σ : State} (pre : In P σ) : VE P σ sE1 = b2n (decide (P.e = 1)) := by
  simp (config := {decide := true}) only [VE, upd, ↓reduceIte]; rw [AE_e pre, AE_one]

/-- The stage normalized after `gcd(c − 1, e)`'s flag. -/
theorem toS3 {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat} {LS : List Nat}
    {σ s : State} (h : St P E A L V LS σ s) (hA : ∀ j ∈ L3, j ∈ L ∧ A σ j = A3 P σ j)
    (hV : ∀ d ∈ LS3, d ∈ LS ∧ V σ d = V3 P σ d) : S3 P E σ s :=
  h.mono hA hV

/-- `c − 1`, `e`, and whether `gcd(c − 1, e) = 1`: Z iff it is. -/
theorem gcdCheck_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] {E : State → Prop} (hE : ∀ σ, E σ → In P σ) :
    VP (S2 P E) (seqs gcdCheck) (fun σ s => S3 P E σ s ∧ s.z = decide (V3 P σ sG = 1)) := by
  simp only [gcdCheck, seqs]
  refine VP.seq (St.psub3 subCm1_taint (by decide) (by simp) (by simp) (by decide) (by decide)) ?_
  refine VP.seq (St.pldPtr (o1 := foE) (o2 := aoEl) (v1 := fun P => P.eP) (v2 := fun P => BitVec.ofNat 32 P.el)
    (by decide) (by decide) fun σ h => ⟨h.wE, h.aEl⟩) ?_
  refine VP.seq (St.pload (src := fun P => P.eP) (k := fun P => P.el) loadE_taint (by decide) fun σ e h =>
    ⟨h.rdE, fun r hr => ?_, h.fE, h.el1, by have := h.el2; have := h.k1; omega⟩) ?_
  · simp only [CP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.sE.symm
    · exact h.oE.symm
    · exact h.uE.symm
    · exact h.eC
    · exact h.eF.sub_right (Offset.sub_base _ (d := 0) (n := 4) (k := 56) (by decide) |> fun s => by
        simpa only [BitVec.add_zero] using s)
  refine VP.seq (St.pbitOf bitEo_taint (by simp) (by decide)) ?_
  refine VP.seq (St.peqS eqE1_taint (by simp) (by simp) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq ((St.pisOne (A := AE P) (L := LE) (V := VE P) (LS := LSE) isEo_taint (by simp)
    fun σ _ => by simp (config := {decide := true}) only [VE, upd, ↓reduceIte]; exact VG.Proof.Rsa.b2n_le _).mono
    (fun σ s h => h.mono (fun j hj => ⟨by mem_sub, rfl⟩) fun j hj => ⟨by mem_sub, rfl⟩) fun _ _ h => h) ?_
  refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
    rw [isa_eq, isa_eq, h₁.2, h₂.2, VE_o (hE σ₁ h₁.1.1), VE_o (hE σ₂ h₂.1.1)]) ?_ ?_)
    (St.pisOne isG_taint (by simp) fun σ _ => by simp only [V3, upd_self]; exact VG.Proof.Rsa.b2n_le _)
  · -- `e` odd.
    refine VP.seq ((St.pisOne (E := fun σ => E σ ∧ P.e % 2 = 1) isE1_taint (by simp)
      fun σ _ => by simp (config := {decide := true}) only [VE, upd, ↓reduceIte]; exact VG.Proof.Rsa.b2n_le _).mono
      (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, ?_⟩) fun _ _ h => h) ?_
    · rw [isa_eq, z, VE_o (hE σ e)] at t; cases h2 : decide (P.e % 2 = 1) <;> simp_all [VG.Proof.Rsa.b2n]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [isa_eq, isa_eq, h₁.2, h₂.2, VE_1 (hE σ₁ h₁.1.1.1), VE_1 (hE σ₂ h₂.1.1.1)]) ?_ ?_
    · -- `e = 1`.
      refine (St.psetS (E := fun σ => (E σ ∧ P.e % 2 = 1) ∧ P.e = 1) g1_taint (by decide) (by decide)
        (by decide)).mono (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, ?_⟩) fun σ s h =>
          (toS3 h (fun j hj => ⟨by mem_sub, ?_⟩) fun j hj => ⟨by mem_sub, ?_⟩).weaken (·.1.1)
      · rw [isa_eq, z, VE_1 (hE σ e.1)] at t; cases h2 : decide (P.e = 1) <;> simp_all [VG.Proof.Rsa.b2n]
      · have pre := hE σ h.1.1.1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [AE_e pre]; simp (config := {decide := true}) only [A3, upd, ↓reduceIte]
        · rw [AE_cm1 pre]; simp (config := {decide := true}) only [A3, upd, ↓reduceIte]
        all_goals simp (config := {decide := true}) only [AE, A3, upd, ↓reduceIte]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl
        · simp only [upd_self, V3, gv_one h.1.2]; rfl
        all_goals simp (config := {decide := true}) only [VE, V3, upd, ↓reduceIte]
    · -- `e` odd and not 1: the inverse modulo `e`.
      refine (VP.seq (St.pinv (E := fun σ => (E σ ∧ P.e % 2 = 1) ∧ P.e ≠ 1) copyME_taint copy0Cm1_taint
        copy2One_taint (by simp) (by simp) (by simp) (by simp) (by decide) (by decide) fun σ e => ?_)
        (St.peqS eqG_taint (by simp) (by simp) (by decide) (by decide) (by decide) (by decide))).mono
        (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, ?_⟩) fun σ s h =>
          (toS3 h (fun j hj => ⟨by mem_sub, ?_⟩) fun j hj => ⟨by mem_sub, ?_⟩).weaken (·.1.1)
      · have pre := hE σ e.1.1
        rw [AE_zero, AE_one, AE_e pre]
        exact ⟨rfl, rfl, e.1.2, by have := e.2; have := e.1.2; omega⟩
      · have t' : some s.z = some false := t
        rw [z, VE_1 (hE σ e.1)] at t'; cases h2 : decide (P.e = 1) <;> simp_all [VG.Proof.Rsa.b2n]
      · have pre := hE σ h.1.1.1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
        · simp (config := {decide := true}) only [upd, ↓reduceIte]; rw [AE_e pre]
          simp (config := {decide := true}) only [A3, upd, ↓reduceIte]
        · simp (config := {decide := true}) only [upd, ↓reduceIte]; rw [AE_cm1 pre]
          simp (config := {decide := true}) only [A3, upd, ↓reduceIte]
        all_goals simp (config := {decide := true}) only [AE, A3, upd, ↓reduceIte]
      · have pre := hE σ h.1.1.1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl
        · simp (config := {decide := true}) only [upd, ↓reduceIte, V3]
          rw [AE_cm1 pre, AE_e pre, AE_one]
          obtain ⟨hodd, hlo, hhi⟩ := cv_shape (σ := σ) pre
          have p8 : 2 ^ (8 * P.L) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by simp only [CP.W]; omega)
          have p64 : 2 ^ 64 ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by have := pre.wge; omega)
          have := e_lt pre
          rw [(ivr_spec (W := P.W) (a := cv P σ - 1) (m := P.e) h.1.1.2 (by have := h.1.2; have := h.1.1.2; omega)
            (by omega) (by omega)).1]
          unfold gv
          by_cases hg : (cv P σ - 1).gcd P.e = 1
          · simp [hg]
          · rw [beq_eq_false_iff_ne.mpr hg, decide_eq_false hg]
        all_goals simp (config := {decide := true}) only [VE, V3, upd, ↓reduceIte]
  · -- `e` even.
    refine (St.psetS (E := fun σ => E σ ∧ P.e % 2 = 0) g0_taint (by decide) (by decide)
      (by decide)).mono (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, ?_⟩) fun σ s h =>
        (toS3 h (fun j hj => ⟨by mem_sub, ?_⟩) fun j hj => ⟨by mem_sub, ?_⟩).weaken (·.1)
    · rw [isa_eq, z, VE_o (hE σ e)] at t; cases h2 : decide (P.e % 2 = 1) <;> simp_all [VG.Proof.Rsa.b2n]
    · have pre := hE σ h.1.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [AE_e pre]; simp (config := {decide := true}) only [A3, upd, ↓reduceIte]
      · rw [AE_cm1 pre]; simp (config := {decide := true}) only [A3, upd, ↓reduceIte]
      all_goals simp (config := {decide := true}) only [AE, A3, upd, ↓reduceIte]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl
      · simp only [upd_self, V3, gv_even (hE σ h.1.1) h.1.2]; rfl
      all_goals simp (config := {decide := true}) only [VE, V3, upd, ↓reduceIte]

end

end VG.Proof.RsaKeyGen.Arm.Cand
