module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Exp6
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Exp1
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Exp5
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Exp3
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Seqs
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint5
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Ops
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Rsa.Arm.RvCand2
import VerifiedGarbage.Proof.Rsa.Arm.RvHalving

/-! # A candidate on ARMv7: the round's exponent (`expSetup_vp`)

From `S3`: the exponent of 2 in `c − 1`, `t`, by the halvings; `E = c / 2^σ`
(the round's `exponent c`) into the key array `mBase + 27`, followed by the
word `2^(t mod 64)` (`EX`): the stage `SX`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)

/-- The exponent of 2 in `c − 1`. -/
def tv (P : CP) (σ : State) : Nat := (Spec.Rsa.splitTwos (cv P σ - 1)).1

/-- The round's exponent, followed by the word `2^(t mod 64)`. -/
def EX (P : CP) (σ : State) : Nat :=
  Proof.MillerRabin.Round.exponent (cv P σ) + 2 ^ (32 * (P.W - 2)) * 2 ^ (tv P σ % 64)

def AX (P : CP) (σ : State) : Nat → Nat := upd (A3 P σ) (mBase + 27) (EX P σ)
abbrev LX : List Nat := [mBase + 27, aCm1, aTwo, aOne, aC]

/-- After the exponent. -/
abbrev SX (P : CP) (E : State → Prop) : State → State → Prop := St P E (AX P) LX (V3 P) [sUsed]

section
variable {P : CP}

theorem tv_eq {σ : State} (pre : In P σ) : (hv P σ (8 * P.L)).2 = tv P σ := by
  rw [hv_done σ pre]; rfl

theorem tv_lt {σ : State} (pre : In P σ) : tv P σ < 2 ^ 32 := by
  rw [← tv_eq pre]; have := hv_le (P := P) σ (8 * P.L); have := pre.k2; omega

theorem exp_eq {σ : State} (pre : In P σ) :
    hIf (hIf (hIf (cv P σ / 2) (b2n (decide (tv P σ % 4 ≠ 1)))) (b2n (decide (tv P σ % 4 = 3 ∨ tv P σ % 4 = 0))))
      (b2n (decide (tv P σ % 4 = 0))) = Proof.MillerRabin.Round.exponent (cv P σ) := by
  rw [shift_div]
  unfold Proof.MillerRabin.Round.exponent Proof.MillerRabin.Round.shift
  have hodd := (cv_shape (σ := σ) pre).1
  rw [odd_div hodd (by dsimp only; split <;> omega)]
  rfl

theorem exponent_le (c : Nat) : Proof.MillerRabin.Round.exponent c ≤ c := by
  unfold Proof.MillerRabin.Round.exponent
  exact Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)

theorem expSetup_vp {E : State → Prop} (hE : ∀ σ, E σ → In P σ) :
    VP (S3 P E) (seqs expSetup) (SX P E) := by
  have e0 : expSetup = [halving, .block (sigMasks ++ powWord), copy aEx aC, .block [.mov .r11 (.imm 0)],
      half aEx] ++ (halfIf sS1 ++ (halfIf sS2 ++ (halfIf sS3 ++ [copy (mBase + 27) aEx, .block expTop]))) := rfl
  rw [e0]
  have sgb : ∀ t : Nat, (sg (BitVec.ofNat 32 t)).1.toNat ≤ 1 ∧ (sg (BitVec.ofNat 32 t)).2.1.toNat ≤ 1 ∧
      (sg (BitVec.ofNat 32 t)).2.2.toNat ≤ 1 := fun t => by
    obtain ⟨a, b, c⟩ := sg_val t
    rw [a, b, c]; exact ⟨VG.Proof.Rsa.b2n_le _, VG.Proof.Rsa.b2n_le _, VG.Proof.Rsa.b2n_le _⟩
  have p0 := VP.seq (halving_vp hE) (VP.seq (St.psigPow (A := AH P (8 * P.L)) (L := LH)
    (V := VH P (8 * P.L)) (LS := LSH) sigPow_taint (by simp) fun σ e => by
      simp (config := {decide := true}) only [VH, upd, ↓reduceIte]
      rw [tv_eq (hE σ e)]; exact tv_lt (hE σ e))
    (VP.seq (St.pcopy copyEx_taint (by decide) (by simp) (by decide))
      (VP.seq (St.pmov11 mov11_taint) (St.phalf halfEx_taint (by simp)))))
  have p1 := VP.seqs_app (a := [halving, .block (sigMasks ++ powWord), copy aEx aC, .block [.mov .r11 (.imm 0)],
    half aEx]) (by simp) (by simp [halfIf]) p0 (St.phalfIf selS1_taint (by simp) (by simp) fun σ _ => by
      simp only [VSg, upd, ↓reduceIte]; exact (sgb _).1)
  have p2 := VP.seqs_app (by simp) (by simp [halfIf]) p1 (St.phalfIf selS2_taint (by simp) (by simp) fun σ _ => by
      simp only [VSg, upd, ↓reduceIte]; exact (sgb _).2.1)
  have p3 := VP.seqs_app (by simp) (by simp [halfIf]) p2 (St.phalfIf selS3_taint (by simp) (by simp) fun σ _ => by
      simp only [VSg, upd, ↓reduceIte]; exact (sgb _).2.2)
  have p4 := VP.seqs_app (b := [copy (mBase + 27) aEx, .block expTop]) (by simp) (by simp) p3
    (VP.seq (St.pcopy copyE27_taint (by decide) (by simp) (by decide))
      (St.pexpTop expTop_taint (by simp) (by simp) (by simp) fun σ e pre => ⟨?_, ?_, ?_⟩))
  · simp only [List.append_assoc] at p4
    refine p4.mono (fun _ _ h => h) fun σ s h => h.mono (fun j hj => ⟨by mem_sub, ?_⟩) fun j hj => ⟨by mem_sub, ?_⟩
    · have pre := hE σ h.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl
      · simp (config := {decide := true}) only [upd, ↓reduceIte, AH, A3, A0, VSg, VH, AX, EX]
        rw [(sg_val _).1, (sg_val _).2.1, (sg_val _).2.2, tv_eq pre, exp_eq pre, pw_val]
      all_goals simp (config := {decide := true}) only [upd, ↓reduceIte, AH, AX]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      simp (config := {decide := true}) only [upd, ↓reduceIte, VSg, VH]
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AH, A3, A0, VSg, VH]
    rw [(sg_val _).1, (sg_val _).2.1, (sg_val _).2.2, tv_eq pre, exp_eq pre]
    have := exponent_le (cv P σ)
    have := (cv_shape (σ := σ) pre).2.2
    have p : 2 ^ (8 * P.L) = 2 ^ (32 * (P.W - 2)) := by have := pre.W_eq; have := pre.L_eq; congr 1; omega
    omega
  · simp (config := {decide := true}) only [upd, ↓reduceIte, VSg]; exact BitVec.isLt _
  · simp (config := {decide := true}) only [upd, ↓reduceIte, VSg]; exact BitVec.isLt _

end

end VG.Proof.RsaKeyGen.Arm.Cand
