module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Range
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Q
public import VerifiedGarbage.Proof.Dsa.RandomResult
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# DSA sampling on PPC64LE: a draw

* `shortTest_ok`: `r3 = 1` exactly when the tape has fewer than `W` octets
  left;
* `copyRange_ok`: `copy` then `inRange`, `r6 = 1` exactly when the draw's
  candidate is accepted, and the nonce's last `W` octets are the candidate;
* `drawFinish_ok`: the status after the candidate's test;
* `draw_ok`: a draw, against `Random.sample`: either the specification's
  sampling ends there (the status is its status), or it rejects the
  candidate and goes on with a draw fewer.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont
open VG.Spec.Dsa.Random (sample candidate drawBytes)
open VG.Proof.Dsa.Random (sampleStatus)

theorem shortTest_ok {E : SE} {R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (h : SEnv E R s)
    (h25 : s.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl) :
    WP isa (.block shortTest) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if E.rl - u < E.W then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.r3, .r4, .r5] s t := by
  have hrn := hE.rl
  have hW := hE.Wq
  have hql := hE.ql
  refine WP.keep _ ?_ (by decide)
  unfold shortTest
  prun [h.r24, h25, h.r28, VG.Offset.ofNat_sub_ofNat hu, short_eq (x := E.rl - u) (w := E.W) (by omega) (by omega)]

/-- What `drawFinish` decides. -/
theorem drawFinish_ok {s : State} {d : Nat} {a : Bool} (h17 : s.gpr .r17 = BitVec.ofNat 64 d) (hd : 1 ≤ d)
    (hd' : d < 2 ^ 64) (h6 : s.gpr .r6 = BitVec.ofNat 64 (if a then 1 else 0)) :
    WP isa drawFinish s fun t =>
      t.mem = s.mem ∧ Keep [.r17, .r31] s t ∧ (a = true → t.gpr .r31 = BitVec.ofNat 64 1) ∧
        (a = false → t.gpr .r17 = BitVec.ofNat 64 (d - 1) ∧ (d = 1 → t.gpr .r31 = BitVec.ofNat 64 0) ∧
          (d ≠ 1 → t.gpr .r31 = s.gpr .r31)) := by
  unfold drawFinish
  refine WP.ite (a == true) ?_ (fun ha => ?_) (fun ha => ?_)
  · rw [VG.PPC64LE.eval_nonzero, h6]; cases a <;> rfl
  · simp only [beq_iff_eq] at ha
    refine WP.mono (WP.keep [.r17, .r31] (Q := fun t => t.mem = s.mem ∧ t.gpr .r31 = BitVec.ofNat 64 1)
      (by prun) (by decide)) fun t ⟨⟨tm, t31⟩, k⟩ => ⟨tm, k, fun _ => t31, fun h => by rw [ha] at h; cases h⟩
  · have ha' : a = false := by cases a <;> simp_all
    subst ha'
    refine WP.seq (WP.mono (WP.keep [.r17] (Q := fun t => t.mem = s.mem ∧
      t.gpr .r17 = BitVec.ofNat 64 (d - 1)) (by prun [h17, VG.Offset.ofNat_sub_ofNat hd]) (by decide))
      fun t₁ ⟨⟨m1, a17⟩, k1⟩ => ?_)
    refine WP.ite (decide (d - 1 = 0)) (eval_zero_ofNat _ _ (by omega) a17) (fun hz => ?_) (fun hz => ?_)
    · simp only [decide_eq_true_eq] at hz
      refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r31 = BitVec.ofNat 64 0)
        (by prun) (by decide)) fun t ⟨⟨tm, t31⟩, k⟩ => ⟨tm.trans m1, (k1.trans k).mono (by decide),
          (fun h => by cases h), fun _ => ⟨(k.gpr .r17 (by decide)).trans a17, fun _ => t31,
            fun h => absurd (by omega) h⟩⟩
    · simp only [decide_eq_false_iff_not] at hz
      refine WP.mono (WP.block_nil rfl) fun t ht => ?_
      subst ht
      exact ⟨m1, k1.mono (by decide), (fun h => by cases h), fun _ => ⟨a17, fun h => absurd (by omega) hz,
        fun _ => k1.gpr .r31 (by decide)⟩⟩

end VG.Proof.Dsa.PPC64LE.Rnd

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont
open VG.Spec.Dsa.Random (sample candidate drawBytes)
open VG.Proof.Dsa.Random (sampleStatus)

/-- Whether the draw at `u` is accepted. -/
abbrev acc (qb R : List Byte) (u W : Nat) : Prop :=
  0 < candidate (Spec.Dsa.decodeBE qb) ((R.drop u).take W) ∧
    candidate (Spec.Dsa.decodeBE qb) ((R.drop u).take W) < Spec.Dsa.decodeBE qb

/-- `copy` then `inRange`: the candidate in the nonce, and whether it is accepted. -/
theorem copyRange_ok {E : SE} {qb R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h25 : s.gpr .r25 = BitVec.ofNat 64 u) (hu : u + E.W ≤ E.rl) :
    WP isa (.seq copy inRange) s fun t =>
      (SEnv E R t ∧ Outside E.F E.o E.W s.mem t.mem ∧ t.gpr .r25 = BitVec.ofNat 64 (u + E.W) ∧
        t.gpr .r6 = BitVec.ofNat 64 (if acc qb R u E.W then 1 else 0) ∧
        Spec.Dsa.decodeBE (cands E t.mem) = candidate (Spec.Dsa.decodeBE qb) ((R.drop u).take E.W)) ∧
      Keep (copyRegs ++ rangeRegs) s t := by
  have hRl := h.R_length
  refine WP.seq (WP.mono (copy_ok hE h h25 hu) fun s₁ ⟨⟨a25, o1, cb⟩, k1⟩ => ?_)
  have h1 : SEnv E R s₁ := h.step hE k1 (o := E.ql - E.W) (n := E.W) (by have := hE.ql; have := hE.Wq; omega) o1
  have hc : cands E s₁.mem = cpyList (R.drop u) E.M E.W := by
    apply List.ext_getElem
    · simp [cands, VG.Proof.Bignum.bytesAt_length]
    · intro j hj _
      simp only [cands, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, cpyList]
      rw [← cb j (by simpa [VG.Proof.Bignum.bytesAt_length] using hj), off_add]
  have hcand : Spec.Dsa.decodeBE (cands E s₁.mem) = candidate (Spec.Dsa.decodeBE qb) ((R.drop u).take E.W) := by
    rw [hc, hQ.cand (by rw [List.length_drop]; omega)]
  refine WP.mono (inRange_ok hE h1) fun t ⟨⟨a6, tm⟩, k2⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, k1.trans k2⟩
  · exact h1.step hE k2 (o := 0) (n := 0) (by omega) (by rw [tm]; exact Outside.refl _ _ _ _)
  · rw [tm]; exact o1
  · rw [k2.gpr .r25 (by decide)]; exact a25
  · rw [a6, hcand, hQ.qs_val]
  · rw [tm]; exact hcand

/-- The registers a draw writes. -/
def drawRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r17, .r25, .r31]

/-- A rejected draw of `W` octets, then `S`. -/
abbrev rejectOf (W : Nat) (S : Spec.Dsa.Random.Sample) : Spec.Dsa.Random.Sample :=
  { S with used := W + S.used, trace := 0 :: S.trace }

theorem draw_ok {E : SE} {qb R : List Byte} {s : State} {u d : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h25 : s.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl)
    (h17 : s.gpr .r17 = BitVec.ofNat 64 d) (hd : 1 ≤ d) (hd' : d ≤ 128) (h31 : s.gpr .r31 = BitVec.ofNat 64 4) :
    WP isa draw s fun t =>
      SEnv E R t ∧ Outside E.F E.o E.W s.mem t.mem ∧ Keep drawRegs s t ∧
        ((t.gpr .r31 = BitVec.ofNat 64 4 ∧ 2 ≤ d ∧ t.gpr .r17 = BitVec.ofNat 64 (d - 1) ∧
            t.gpr .r25 = BitVec.ofNat 64 (u + E.W) ∧ u + E.W ≤ E.rl ∧
            sample (Spec.Dsa.decodeBE qb) d (R.drop u) =
              rejectOf E.W (sample (Spec.Dsa.decodeBE qb) (d - 1) (R.drop (u + E.W)))) ∨
          (t.gpr .r31 = BitVec.ofNat 64 (sampleStatus (sample (Spec.Dsa.decodeBE qb) d (R.drop u))) ∧
            t.gpr .r25 = BitVec.ofNat 64 (u + (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).used) ∧
            ∀ k, (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).scalar = some k →
              Spec.Dsa.decodeBE (cands E t.mem) = k)) := by
  have hRl := h.R_length
  have hq := hQ.gt
  have hdw := hQ.draw
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hlen : (R.drop u).length = E.rl - u := by rw [List.length_drop, hRl]
  unfold draw
  refine WP.seq (WP.mono (shortTest_ok hE h h25 hu) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have h1 : SEnv E R s₁ := h.step hE k1 (o := 0) (n := 0) (by omega) (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.ite (decide (E.rl - u < E.W)) ?_ (fun hs => ?_) (fun hs => ?_)
  · rw [eval_nonzero_ofNat' _ _ (by split <;> decide) a3]
    congr 1
    by_cases hc : E.rl - u < E.W <;> simp [hc]
  · simp only [decide_eq_true_eq] at hs
    refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = s₁.mem ∧ t.gpr .r31 = BitVec.ofNat 64 2)
      (by prun) (by decide)) fun t ⟨⟨tm, t31⟩, k2⟩ => ⟨h1.step hE k2 (o := 0) (n := 0) (by omega)
        (by rw [tm]; exact Outside.refl _ _ _ _), by rw [tm, m1]; exact Outside.refl _ _ _ _,
        (k1.trans k2).mono (by decide), .inr ?_⟩
    have hS : sample (Spec.Dsa.decodeBE qb) (d' + 1) (R.drop u) = ⟨none, 0, [2]⟩ :=
      Dsa.Random.sample_short _ _ _ hq (by rw [hlen, hdw]; exact hs)
    rw [hS, t31, (k2.gpr .r25 (by decide)).trans ((k1.gpr .r25 (by decide)).trans h25)]
    exact ⟨rfl, rfl, fun k hk => by cases hk⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hs
    have h25' : s₁.gpr .r25 = BitVec.ofNat 64 u := (k1.gpr .r25 (by decide)).trans h25
    refine WP.seq (WP.mono (copyRange_ok hE hQ h1 h25' (by omega)) fun s₂ ⟨⟨h2, o2, a25, a6, hc⟩, k2⟩ => ?_)
    have a17 : s₂.gpr .r17 = BitVec.ofNat 64 (d' + 1) := (k2.gpr .r17 (by decide)).trans ((k1.gpr .r17 (by decide)).trans h17)
    have hs' : drawBytes (Spec.Dsa.decodeBE qb) ≤ (R.drop u).length := by rw [hlen, hdw]; exact hs
    refine WP.mono (drawFinish_ok (a := decide (acc qb R u E.W)) a17 (by omega) (by omega)
      (by
        rw [a6]
        by_cases ha : acc qb R u E.W
        · rw [ite_eq_left ha, ite_eq_left (show decide (acc qb R u E.W) = true from decide_eq_true ha)]
        · rw [ite_eq_right ha, ite_eq_right (show ¬ decide (acc qb R u E.W) = true by simpa using ha)]))
      fun t ⟨tm, k3, hacc, hrej⟩ => ⟨h2.step hE k3 (o := 0) (n := 0) (by omega) (by rw [tm]; exact Outside.refl _ _ _ _),
        by rw [tm, ← m1]; exact o2, ((k1.trans k2).trans k3).mono (by decide), ?_⟩
    have t25 : t.gpr .r25 = BitVec.ofNat 64 (u + E.W) := (k3.gpr .r25 (by decide)).trans a25
    by_cases ha : acc qb R u E.W
    · have hS := Dsa.Random.sample_accept _ d' _ hq hs' (by rw [hdw]; exact ha)
      rw [hdw] at hS
      refine .inr ⟨?_, ?_, ?_⟩
      · rw [hacc (by simp [ha]), hS]; rfl
      · rw [t25, hS]
      · intro k hk
        rw [hS] at hk
        cases hk
        rw [tm]; exact hc
    · have hS := Dsa.Random.sample_reject _ d' _ hq hs' (by rw [hdw]; exact ha)
      rw [hdw, List.drop_drop] at hS
      obtain ⟨r17', r31z, r31k⟩ := hrej (by simp [ha])
      by_cases hd1 : d' = 0
      · subst hd1
        refine .inr ⟨?_, ?_, ?_⟩
        · rw [r31z rfl, hS]; rfl
        · rw [t25, hS]; rfl
        · intro k hk; rw [hS] at hk; cases hk
      · refine .inl ⟨?_, by omega, r17', t25, by omega, ?_⟩
        · rw [r31k (by omega), (k2.gpr .r31 (by decide)).trans ((k1.gpr .r31 (by decide)).trans h31)]
        · rw [hS, Nat.add_sub_cancel]

end VG.Proof.Dsa.PPC64LE.Rnd
