module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Fin2
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: Miller–Rabin's result (`mrPart_vp`)

The status after Miller–Rabin is public (`statQ_eq`: it is `statS` of the
branches), and its result: status 0 if `rand` was too short, 1 and the
candidate for a probable prime, 3 for a composite (`outM`, `usedM`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.MillerRabin.Arm (RoundImpl)

/-- The status from the shape of Miller–Rabin's result. -/
def statS : Option (Bool × Nat) → Nat
  | none => 0
  | some (true, _) => 1
  | some (false, _) => 3

/-- `out` and `used` after Miller–Rabin. -/
def outM (P : CP) (σ : State) : List Byte :=
  if statQ P σ = 1 then Spec.Rsa.i2osp (cv P σ) P.L else List.replicate P.L 0
def usedM (P : CP) (σ : State) : Nat := if statQ P σ = 0 then 0 else usedQ P σ

theorem statS_vals (x : Option (Bool × Nat)) : statS x = 0 ∨ statS x = 1 ∨ statS x = 3 := by
  rcases x with _ | ⟨_ | _, _⟩ <;> simp [statS]

section
variable {P : CP} {E : State → Prop}

theorem statQ_eq {σ : State} (pre : In P σ) (hm : EM P σ) : statQ P σ = statS P.sch.mr := by
  rw [(mr_facts pre hm).1]
  unfold statQ
  rcases resP P σ with _ | ⟨_ | _, _⟩ <;> rfl

/-- The comparison of `sStat` with `c`. -/
theorem statCmp_vp {c : BitVec 32} {k : Nat} (cert : Cert (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm c)]))
    (hc : encodable c = true) (hz : ∀ v ∈ [0, 1, 3], (BitVec.ofNat 32 v - c == 0) = decide (v = k)) :
    VP (QS P E) (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm c)])
      (fun σ s => QS P E σ s ∧ s.z = decide (statQ P σ = k)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    refine h.ldr hw (d := sStat) (by simp) (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine wp_cmp (op2_imm hc) fun t f z => WP.block_nil ⟨⟨e, h1.of_rest (f.rest []) f.mem,
      hw1.of (by rw [f.gpr]) (by rw [f.gpr]) (by rw [f.gpr]) f.wr⟩, ?_⟩
    rw [z, u1.gpr]
    simp only [upd_self]
    exact hz _ (by unfold statQ; split <;> simp)

theorem stat_of {σ s : State} {k : Nat} (pre : In P σ) (hm : EM P σ) (z : s.z = decide (statQ P σ = k))
    {b : Bool} (t : isa.eval .eq s = some b) : decide (statS P.sch.mr = k) = b := by
  rw [isa_eq, z, statQ_eq pre hm] at t
  simpa using t

/-- Miller–Rabin's result. -/
theorem mrResult_vp (hE : ∀ σ, E σ → In P σ ∧ EM P σ) :
    VP (QS P E) mrResult (RF P E (statQ P) (outM P) (usedM P)) := by
  simp only [mrResult]
  refine VP.seq (statCmp_vp (k := 0) stat0_cmp_taint (by decide) (by decide)) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · rw [isa_eq, isa_eq, h₁.2, h₂.2, statQ_eq (hE σ₁ h₁.1.1).1 (hE σ₁ h₁.1.1).2,
      statQ_eq (hE σ₂ h₂.1.1).1 (hE σ₂ h₂.1.1).2]
  · refine VP.ofImp (p := statS P.sch.mr = 0) (fun σ s h => by
      have := stat_of (hE σ h.1.1.1).1 (hE σ h.1.1.1).2 h.1.2 h.2; simpa using this) fun hs => ?_
    refine finNone_vp.mono (fun σ s h => ⟨h.1.1.1, h.1.1.2.1.bk⟩) fun σ s ⟨e, b, r0, o, u⟩ => ?_
    have hq : statQ P σ = 0 := by rw [statQ_eq (hE σ e).1 (hE σ e).2, hs]
    refine ⟨e, b, by rw [r0, hq], by rw [o, outM, hq]; rfl, by rw [u, usedM, hq]; rfl⟩
  · refine VP.ofImp (p := statS P.sch.mr ≠ 0) (fun σ s h => by
      have := stat_of (hE σ h.1.1.1).1 (hE σ h.1.1.1).2 h.1.2 h.2; simpa using this) fun hs0 => ?_
    refine VP.seq ((statCmp_vp (k := 1) stat1_cmp_taint (by decide) (by decide)).mono (fun σ s h => h.1.1)
      fun _ _ h => h) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) ?_ ?_
    · rw [isa_eq, isa_eq, h₁.2, h₂.2, statQ_eq (hE σ₁ h₁.1.1).1 (hE σ₁ h₁.1.1).2,
        statQ_eq (hE σ₂ h₂.1.1).1 (hE σ₂ h₂.1.1).2]
    · refine VP.ofImp (p := statS P.sch.mr = 1) (fun σ s h => by
        have := stat_of (hE σ h.1.1.1).1 (hE σ h.1.1.1).2 h.1.2 h.2; simpa using this) fun hs => ?_
      refine (finPrime_vp (by decide) (by simp) fun σ e => ?_).mono (fun σ s h => h.1.1)
        fun σ s ⟨e, b, r0, o, u⟩ => ?_
      · have pre := (hE σ e).1
        have := cv_lt pre
        have := pre.L_eq
        simp (config := {decide := true}) only [AB2, AX, A3, A0, upd, ↓reduceIte]
        rwa [show 8 * P.L = 64 * P.w by omega]
      · have hq : statQ P σ = 1 := by rw [statQ_eq (hE σ e).1 (hE σ e).2, hs]
        refine ⟨e, b, by rw [r0, hq], ?_, ?_⟩
        · rw [o, outM, hq]
          simp (config := {decide := true}) only [AB2, AX, A3, A0, upd, ↓reduceIte]
        · rw [u, usedM, hq]
          simp (config := {decide := true}) only [upd, ↓reduceIte]
    · refine VP.ofImp (p := statS P.sch.mr ≠ 1) (fun σ s h => by
        have := stat_of (hE σ h.1.1.1).1 (hE σ h.1.1.1).2 h.1.2 h.2; simpa using this) fun hs1 => ?_
      have hs : statS P.sch.mr = 3 := by
        rcases statS_vals P.sch.mr with h | h | h
        · exact absurd h hs0
        · exact absurd h hs1
        · exact h
      refine (finUsed_vp finTail3_taint (by decide) (by decide) (by simp)).mono (fun σ s h => h.1.1)
        fun σ s ⟨e, b, r0, o, u⟩ => ?_
      have hq : statQ P σ = 3 := by rw [statQ_eq (hE σ e).1 (hE σ e).2, hs]
      refine ⟨e, b, by rw [r0, hq], by rw [o, outM, hq]; rfl, ?_⟩
      rw [u, usedM, hq]
      simp (config := {decide := true}) only [upd, ↓reduceIte]

/-- Once the candidate passed trial division and `gcd(c − 1, e) = 1`. -/
theorem mrPart_vp (v : RoundImpl) (hE : ∀ σ, E σ → In P σ ∧ EM P σ) :
    VP (S3 P E) (mrPart v.name v.code) (RF P E (statQ P) (outM P) (usedM P)) :=
  VP.seqs_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (expSetup_vp fun σ e => (hE σ e).1)
    (montA_vp.seq (montB_vp.seq ((millerRabin_vp v hE).seq (mrResult_vp hE))))

end

end VG.Proof.RsaKeyGen.Arm.Cand
