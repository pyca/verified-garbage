module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Load1
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Inv
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint3
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Ops
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads
import VerifiedGarbage.Proof.Rsa.RecoverSubtract
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Loads

/-! # DSA's probable-prime test on ARMv7: the stages before Miller–Rabin

From `S0` (`Load1.lean`): trial division writes the header word `sTr` :=
whether the candidate is obviously composite (`compv`), the stage `S2`; then
`c − 1` into `aCm1`, the stage `S3` from which RSA's exponent setup runs.
RSA's candidate has two more checks between them (too close to `p`, and
`gcd(c − 1, e)`), whose header words `sCl` and `sG` these stages lack.
Loads of arrays on a stage (`St.pload`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 sub32_of)
open VG.Proof.Rsa (b2n)

/-- The header words before trial division. -/
def V1 (P : CP) (_σ : State) : Nat → Nat := V0 P

abbrev L1 : List Nat := [aTwo, aOne, aC, aZero]

/-- Whether the candidate is obviously composite, and the header words after
trial division. -/
def compv (P : CP) (σ : State) : Bool := Spec.RsaKeyGen.obviouslyComposite P.bits (cv P σ)
def V2 (P : CP) (σ : State) : Nat → Nat := upd (V1 P σ) sTr (b2n (compv P σ))

/-- After trial division. -/
abbrev S2 (P : CP) (E : State → Prop) : State → State → Prop := St P E (A0 P) L1 (V2 P) [sTr, sUsed]

abbrev S1 (P : CP) (E : State → Prop) : State → State → Prop := St P E (A0 P) L1 (V1 P) [sUsed]

/-- The arrays after `c − 1`. -/
def A3 (P : CP) (σ : State) : Nat → Nat := upd (A0 P σ) aCm1 (cv P σ - 1)

abbrev L3 : List Nat := [aCm1, aTwo, aOne, aC, aZero]

def V3 (P : CP) (σ : State) : Nat → Nat := V2 P σ

abbrev LS3 : List Nat := [sTr, sUsed]

abbrev S3 (P : CP) (E : State → Prop) : State → State → Prop := St P E (A3 P) L3 (V3 P) LS3

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `load j`: `[j] :=` the `k` octets at `r4` (`r6 = k`). -/
theorem St.pload {j : Nat} {src : CP → BitVec 32} {k : CP → Nat} (cert : LCert j) (hj : j < nArr)
    (hin : ∀ σ, E σ → In P σ → InRegions (σ.rd ++ σ.wr) (State.addr (src P)) (k P) ∧
      (∀ r ∈ P.chg, Region.Disjoint ⟨State.addr (src P), k P⟩ r) ∧
      (src P).toNat + k P ≤ 2 ^ 32 ∧ 0 < k P ∧ k P ≤ P.L) :
    VP (fun σ s => St P E A L V LS σ s ∧ s.gpr .r4 = src P ∧ s.gpr .r6 = BitVec.ofNat 32 (k P))
      (VG.Impl.Rsa.Arm.CrtValues.load j)
      (St P E (fun σ => upd (A σ) j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (src P)) (k P))))
        (j :: L) V LS) := by
  refine VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, p4, p6⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
  · obtain ⟨rd, sC, fit, hk, hkL⟩ := hin σ e h.pre
    refine WP.mono (load_okC h.bk hw hj rd sC fit hk hkL p4 p6) fun t ⟨_, wt, kp, v, r⟩ => ⟨e, ?_, wt⟩
    have hv : num t.mem P.B P.W j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (src P)) (k P)) := by
      have lt : Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (src P)) (k P)) < 2 ^ (32 * P.W) := by
        have := VG.Proof.Rsa.lt_of_os2ip (Spec.Rsa.bytesAt σ.mem (State.addr (src P)) (k P))
        rw [bytesAt_length, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
        exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by simp only [CP.W]; omega))
      rw [← v] at lt ⊢
      exact VG.Proof.Rsa.Arm.CrtValues.val32_low2 lt
    exact h.write1 kp hj (by simp) r.sp r.rd r.wr hv (by simp)

theorem St.weaken {E E' : State → Prop} {σ s : State} (h : St P E A L V LS σ s) (he : E σ → E' σ) :
    St P E' A L V LS σ s :=
  ⟨he h.1, h.2⟩

end

theorem isa_eq (s : State) : isa.eval .eq s = some s.z := rfl

theorem sub32_val {W a b : Nat} (ha : a < 2 ^ (32 * W)) (hb : b < 2 ^ (32 * W)) :
    sub32 W a b = if a < b then a + 2 ^ (32 * W) - b else a - b := by
  unfold sub32
  split
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [show a + 2 ^ (32 * W) - b = a - b + 2 ^ (32 * W) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

section
variable {P : CP}

theorem toS3 {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat} {LS : List Nat}
    {σ s : State} (h : St P E A L V LS σ s) (hA : ∀ j ∈ L3, j ∈ L ∧ A σ j = A3 P σ j)
    (hV : ∀ d ∈ LS3, d ∈ LS ∧ V σ d = V3 P σ d) : S3 P E σ s :=
  h.mono hA hV

/-- `c − 1`. -/
theorem cm1_vp {E : State → Prop} : VP (S2 P E) (sub3 aCm1 aC aOne) (S3 P E) := by
  refine (St.psub3 subCm1_taint (by decide) (by simp) (by simp) (by decide) (by decide)).mono (fun _ _ h => h)
    fun σ s h => toS3 h (fun j hj => ⟨by mem_sub, ?_⟩) fun d hd => ⟨hd, rfl⟩
  have pre := h.2.1.pre
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · simp (config := {decide := true}) only [A3, A0, upd, ↓reduceIte]
    obtain ⟨hodd, -, hhi⟩ := cv_shape (σ := σ) pre
    have p8 : 2 ^ (8 * P.L) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by simp only [CP.W]; omega)
    have p1 : 1 < 2 ^ (32 * P.W) := Nat.one_lt_two_pow (by have := pre.wge; omega)
    rw [sub32_val (by omega) p1]
    simp only [show ¬ cv P σ < 1 by omega, ↓reduceIte]
  all_goals simp (config := {decide := true}) only [A3, A0, upd, ↓reduceIte]

end

end VG.Proof.Dsa.Arm.Prime
