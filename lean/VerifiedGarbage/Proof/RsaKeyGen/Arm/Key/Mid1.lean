module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Front4
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: `e`'s flags, and `d` for `e = 0` and `e = 1`

`SE`: the stage after `e`'s flags (`eFlags_vp`); `G4`: after `d` and its
flag `sOk` (`dv`, `okv`), which every case of `e` ends at.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

/-- The arrays after `lcm(p − 1, q − 1)`. -/
abbrev AS3 (P : KP) (σ : State) : Nat → Nat := upd (AH P σ (8 * P.K)) aL (lv P σ)
abbrev L3 : List Nat := aL :: LH

/-- `e`'s flags. -/
def VE (P : KP) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) sE0 (b2n (decide (P.e = 0)))) sE1 (b2n (decide (P.e = 1)))) sEo
    (b2n (decide (P.e % 2 = 1)))

abbrev SE (P : KP) (E : State → Prop) : State → State → Prop :=
  St P E (AS3 P) L3 (fun _ => VE P) [sEo, sE1, sE0]

/-- After `d`. -/
abbrev G4 (P : KP) (E : State → Prop) : State → State → Prop :=
  St P E (fun σ => upd (AS3 P σ) aD (dv P σ)) (aD :: L3) (fun σ => upd (VE P) sOk (b2n (okv P σ)))
    [sOk, sEo, sE1, sE0]

section
variable {P : KP} {σ : State}

theorem AH_e {k : Nat} : AH P σ k aE = P.e := by simp (config := {decide := true}) only [AH, A1, A0, Aload, upd, ↓reduceIte]
theorem AH_zero {k : Nat} : AH P σ k aZero = 0 := by
  simp (config := {decide := true}) only [AH, A1, A0, Aload, upd, ↓reduceIte]
theorem AH_one {k : Nat} : AH P σ k aOne = 1 := by simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AH_two {k : Nat} : AH P σ k aTwo = 2 := by simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AH_three {k : Nat} : AH P σ k aThree = 3 := by
  simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AH_mod {k : Nat} : AH P σ k aMod = 2 ^ (32 * P.W - 1) := by
  simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AH_D {k : Nat} : AH P σ k aD = 0 := by
  simp (config := {decide := true}) only [AH, A1, A0, Aload, upd, ↓reduceIte]
theorem AH_top {k : Nat} : AH P σ k aTop = 2 ^ (16 * P.K - 1) := by
  simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AH_c33 {k : Nat} : AH P σ k aC33 = 2 ^ 33 := by
  simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AH_P {k : Nat} : AH P σ k aP = pv P σ := by simp (config := {decide := true}) only [AH, A1, upd, ↓reduceIte]
theorem AH_Q {k : Nat} : AH P σ k aQ = qv P σ := by simp (config := {decide := true}) only [AH, A1, upd, ↓reduceIte]
theorem AH_Pm {k : Nat} : AH P σ k aPm = pm P σ := by simp (config := {decide := true}) only [AH, A1, upd, ↓reduceIte]
theorem AH_Qm {k : Nat} : AH P σ k aQm = qm P σ := by simp (config := {decide := true}) only [AH, A1, upd, ↓reduceIte]

theorem AS3_e : AS3 P σ aE = P.e := by simp (config := {decide := true}) only [AH, A1, A0, Aload, upd, ↓reduceIte]
theorem AS3_zero : AS3 P σ aZero = 0 := by
  simp (config := {decide := true}) only [AH, A1, A0, Aload, upd, ↓reduceIte]
theorem AS3_one : AS3 P σ aOne = 1 := by simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AS3_two : AS3 P σ aTwo = 2 := by simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AS3_three : AS3 P σ aThree = 3 := by simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AS3_mod : AS3 P σ aMod = 2 ^ (32 * P.W - 1) := by
  simp (config := {decide := true}) only [AH, A1, A0, upd, ↓reduceIte]
theorem AS3_L : AS3 P σ aL = lv P σ := by simp (config := {decide := true}) only [upd, ↓reduceIte]
theorem AS3_D : AS3 P σ aD = 0 := by
  simp (config := {decide := true}) only [AH, A1, A0, Aload, upd, ↓reduceIte]
theorem VE_0 : VE P sE0 = b2n (decide (P.e = 0)) := by simp (config := {decide := true}) only [VE, upd, ↓reduceIte]
theorem VE_1 : VE P sE1 = b2n (decide (P.e = 1)) := by simp (config := {decide := true}) only [VE, upd, ↓reduceIte]
theorem VE_o : VE P sEo = b2n (decide (P.e % 2 = 1)) := by
  simp (config := {decide := true}) only [VE, upd, ↓reduceIte]

theorem b2n_eq_one_iff (p : Prop) [Decidable p] : b2n (decide p) = 1 ↔ p := by
  by_cases h : p <;> simp [h, b2n]

/-- `e`'s flags. -/
theorem eFlags_vp {E : State → Prop} : VP (S3 P E) eFlags (SE P E) := by
  simp only [eFlags, seqs]
  refine VP.seq (St.peqS eqE0_taint (by simp) (by simp) (by decide) (by decide) (by simp) (by decide)) ?_
  refine VP.seq (St.peqS eqE1_taint (by simp) (by simp) (by decide) (by decide) (by decide) (by decide)) ?_
  refine (St.pbitOf bitEo_taint (by simp) (by decide)).mono (fun _ _ h => h) fun σ s h =>
    h.mono (fun j hj => ⟨hj, rfl⟩) fun d hj => ⟨hj, ?_⟩
  mem_cases <;> simp (config := {decide := true}) only [VE, upd, ↓reduceIte, AH_e, AH_zero, AH_one]

end

end VG.Proof.RsaKeyGen.Arm.Key
