module

import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Q
public import VerifiedGarbage.Proof.Dsa.RandomResult
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Copy
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck

/-! ### `Dsa.PPC64LE.Random.Draw`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Random.Range`, which this module and modules that import it used -/

section

/-!
# DSA sampling on PPC64LE: the candidate's range

`inRange_ok`: `inRange` compares the nonce's last `W` octets (the candidate
`cands`) with q's significant octets, from the least significant, by a
borrow chain (`randomBorrow`) and an or of the candidate's octets
(`randomOr`), and leaves in `r6` whether `0 < candidate < q`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont
open VG.Proof.Dsa (randomBorrow randomOr)

/-- The registers `inRange` writes. -/
def rangeRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8]

/-- The candidate: the nonce's last `W` octets. -/
abbrev cands (E : SE) (m : Mem) : List Byte := Spec.Rsa.bytesAt m (off E.F E.o) E.W

theorem randomOr_lt : ∀ bs : List Byte, (randomOr bs).toNat < 256
  | [] => by decide
  | b :: bs => by
    show (randomOr bs ||| b.setWidth 64).toNat < 256
    rw [BitVec.toNat_or, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]
    exact or_lt (randomOr_lt bs) b.isLt

theorem setWidth_byte (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem drop_cons_getD {bs : List Byte} {k : Nat} (hk : k < bs.length) :
    bs.drop k = bs.getD k 0 :: bs.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl

theorem inRange_ok {E : SE} {R : List Byte} {s : State} (hE : E.Ok) (h : SEnv E R s) :
    WP isa inRange s fun t =>
      (t.gpr .r6 = BitVec.ofNat 64 (if 0 < Spec.Dsa.decodeBE (cands E s.mem) ∧
          Spec.Dsa.decodeBE (cands E s.mem) < Spec.Dsa.decodeBE E.qs then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep rangeRegs s t := by
  have hf := hE.fnw
  have hW1 := hE.W1
  have hWq := hE.Wq
  have hql := hE.ql
  have hqn := hE.qnw
  simp only [frameBytes] at hf
  refine WP.keep rangeRegs ?_ (by decide)
  unfold inRange Precompute.countLoop
  have hi : WP isa (.block rangeInit) s fun s₁ =>
      s₁.gpr .r3 = off E.F (E.o + E.W) ∧ s₁.gpr .r4 = off E.qp E.W ∧ s₁.gpr .r5 = BitVec.ofNat 64 E.W ∧
        s₁.gpr .r6 = BitVec.ofNat 64 0 ∧ s₁.gpr .r7 = 0 ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    unfold rangeInit
    prun [h.r21, h.r27, h.r28, h.sp, exec_addSp (show oNonce < 2 ^ 15 by decide), BitVec.add_zero]
    exact ⟨by rw [show oNonce + E.ql = E.o + E.W by simp only [SE.o]; omega_using [hWq]], rfl⟩
  refine WP.seq (WP.mono hi fun s₁ ⟨i3, i4, i5, i6, i7, im, ird, iwr⟩ => ?_)
  have hcl : (cands E s.mem).length = E.W := VG.Proof.Bignum.bytesAt_length _ _ _
  have hql' : E.qs.length = E.W := hE.qs
  have d1 : (cands E s.mem).drop E.W = [] := List.drop_eq_nil_of_le (by omega_using [hcl])
  have d2 : E.qs.drop E.W = [] := List.drop_eq_nil_of_le (by omega_using [hql'])
  have j6 : s₁.gpr .r6 = BitVec.ofNat 64 (randomBorrow ((cands E s.mem).drop (E.W - 0)) (E.qs.drop (E.W - 0))) := by
    rw [i6, Nat.sub_zero, d1, d2]; rfl
  have j7 : s₁.gpr .r7 = randomOr ((cands E s.mem).drop (E.W - 0)) := by
    rw [i7, Nat.sub_zero, d1]; rfl
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r3 = off E.F (E.o + (E.W - i)) ∧ t.gpr .r4 = off E.qp (E.W - i) ∧
      t.gpr .r6 = BitVec.ofNat 64 (randomBorrow ((cands E s.mem).drop (E.W - i)) (E.qs.drop (E.W - i))) ∧
      t.gpr .r7 = randomOr ((cands E s.mem).drop (E.W - i)) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.seq (WP.mono (wp_countdown (body := .block (rangeByte ++ ([.subi .r5 .r5 1] : List Instr)))
    (cnt := .r5) (N := E.W) (by omega_using [hWq, hql]) (by omega_using [hW1]) Inv
    (fun i hi t ⟨t3, t4, t6, t7, tm, trd, twr⟩ _ => ?_)
    ⟨by rw [i3, Nat.sub_zero], by rw [i4, Nat.sub_zero], j6, j7, im, ird, iwr⟩ i5)
    fun t ht => ?_)
  · have k1 : E.W - i - 1 < E.W := by omega_using [hW1]
    have hrd3 : InRegions (t.rd ++ t.wr) (off E.F (E.o + (E.W - i - 1))) 1 := by
      have := (h.nw.congr twr).ld (d := E.ql - E.W + (E.W - i - 1)) (n := 1) (by omega_using [hW1, hWq, hql])
      rw [off_off, show oNonce + (E.ql - E.W + (E.W - i - 1)) = E.o + (E.W - i - 1) by simp only [SE.o]; omega_using []] at this
      exact this
    have hrd4 : InRegions (t.rd ++ t.wr) (off E.qp (E.W - i - 1)) 1 := by
      rw [trd, twr]; exact h.qr _ k1
    have e3 : off E.F (E.o + (E.W - i)) - BitVec.ofNat 64 1 = off E.F (E.o + (E.W - i - 1)) := by
      rw [off_sub1 _ (by omega_using [hi])]; congr 2; omega_using [hi]
    have e4 : off E.qp (E.W - i) - BitVec.ofNat 64 1 = off E.qp (E.W - i - 1) := by
      rw [off_sub1 _ (by omega_using [hi])]
    have hc : t.mem (off E.F (E.o + (E.W - i - 1))) = (cands E s.mem).getD (E.W - i - 1) 0 := by
      rw [tm]; simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, k1, off_add]
    have hq : t.mem (off E.qp (E.W - i - 1)) = E.qs.getD (E.W - i - 1) 0 := by
      rw [tm]; exact h.qbyte k1
    have hb := Dsa.randomBorrow_le ((cands E s.mem).drop (E.W - i)) (E.qs.drop (E.W - i))
    have hcb := ((cands E s.mem).getD (E.W - i - 1) 0).isLt
    have hqb := (E.qs.getD (E.W - i - 1) 0).isLt
    unfold rangeByte
    prun [t3, t4, t6, t7, e3, e4, exec_lbz' (show Reg.r3 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      exec_lbz' (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd3, hrd4, BitVec.add_zero,
      read_byte64, hc, hq, borrow_eq hcb hqb hb]
    have e1 : E.W - (i + 1) = E.W - i - 1 := by omega_using []
    have e2 : E.W - i - 1 + 1 = E.W - i := by omega_using [hi]
    have hcd : (cands E s.mem).drop (E.W - i - 1) =
        (cands E s.mem).getD (E.W - i - 1) 0 :: (cands E s.mem).drop (E.W - i) := by
      rw [drop_cons_getD (by omega_using [hW1, hcl]), e2]
    have hqd : E.qs.drop (E.W - i - 1) = E.qs.getD (E.W - i - 1) 0 :: E.qs.drop (E.W - i) := by
      rw [drop_cons_getD (by omega_using [hW1, hql']), e2]
    refine ⟨by gsimp; rw [e1], by gsimp; rw [e1], ?_, ?_, by gsimp; exact tm, by gsimp; exact trd, by gsimp; exact twr⟩
    · gsimp
      (rw [e1, hcd, hqd]) <;> rfl
    · gsimp
      (rw [e1, hcd, ← setWidth_byte]) <;> rfl
  · obtain ⟨-, -, t6, t7, tm, -, -⟩ := ht
    simp only [Nat.sub_self, List.drop_zero] at t6 t7
    have hor := randomOr_lt (cands E s.mem)
    unfold rangeFinish
    rw [← VG.Proof.Bignum.ofNat_toNat64 (randomOr (cands E s.mem))] at t7
    prun [t6, t7, nz_eq (x := (randomOr (cands E s.mem)).toNat) (by omega_using [hor])]
    refine ⟨?_, tm⟩
    rw [Dsa.randomBorrow_eq _ _ (by rw [hcl, hql'])]
    have hz := Dsa.randomOr_zero (cands E s.mem)
    have hz' : (randomOr (cands E s.mem)).toNat = 0 ↔ Spec.Dsa.decodeBE (cands E s.mem) = 0 := by
      rw [← hz]
      exact ⟨fun e => BitVec.eq_of_toNat_eq e, fun e => by rw [e]; rfl⟩
    by_cases h1 : Spec.Dsa.decodeBE (cands E s.mem) = 0
    · rw [ite_eq_left (hz'.mpr h1), ite_eq_right (show ¬ (0 < Spec.Dsa.decodeBE (cands E s.mem) ∧ _) by omega_using [h1])]
      split <;> rfl
    · rw [ite_eq_right (fun e => h1 (hz'.mp e))]
      by_cases h2 : Spec.Dsa.decodeBE (cands E s.mem) < Spec.Dsa.decodeBE E.qs
      · rw [ite_eq_left h2, ite_eq_left ⟨by omega_using [h1], h2⟩]; rfl
      · rw [ite_eq_right h2, ite_eq_right (fun h => h2 h.2)]; rfl

end VG.Proof.Dsa.PPC64LE.Rnd

end

end

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
  prun [h.r24, h25, h.r28, VG.Offset.ofNat_sub_ofNat hu, short_eq (x := E.rl - u) (w := E.W) (by omega_using [hrn]) (by omega_using [hW, hql])]

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
    refine WP.ite (decide (d - 1 = 0)) (eval_zero_ofNat _ _ (by omega_using [hd']) a17) (fun hz => ?_) (fun hz => ?_)
    · simp only [decide_eq_true_eq] at hz
      refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r31 = BitVec.ofNat 64 0)
        (by prun) (by decide)) fun t ⟨⟨tm, t31⟩, k⟩ => ⟨tm.trans m1, (k1.trans k).mono (by decide),
          (fun h => by cases h), fun _ => ⟨(k.gpr .r17 (by decide)).trans a17, fun _ => t31,
            fun h => absurd (by omega_using [hd, hz]) h⟩⟩
    · simp only [decide_eq_false_iff_not] at hz
      refine WP.mono (WP.block_nil rfl) fun t ht => ?_
      subst ht
      exact ⟨m1, k1.mono (by decide), (fun h => by cases h), fun _ => ⟨a17, fun h => absurd (by omega_using [h]) hz,
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
  have h1 : SEnv E R s₁ := h.step hE k1 (o := E.ql - E.W) (n := E.W) (by have := hE.ql; have := hE.Wq; omega_arith) o1
  have hc : cands E s₁.mem = cpyList (R.drop u) E.M E.W := by
    apply List.ext_getElem
    · simp [cands, VG.Proof.Bignum.bytesAt_length]
    · intro j hj _
      simp only [cands, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, cpyList]
      rw [← cb j (by simpa [VG.Proof.Bignum.bytesAt_length] using hj), off_add]
  have hcand : Spec.Dsa.decodeBE (cands E s₁.mem) = candidate (Spec.Dsa.decodeBE qb) ((R.drop u).take E.W) := by
    rw [hc, hQ.cand (by rw [List.length_drop]; omega_using [hu, hRl])]
  refine WP.mono (inRange_ok hE h1) fun t ⟨⟨a6, tm⟩, k2⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, k1.trans k2⟩
  · exact h1.step hE k2 (o := 0) (n := 0) (by omega_using []) (by rw [tm]; exact Outside.refl _ _ _ _)
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
            (∀ k, (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).scalar = some k →
              Spec.Dsa.decodeBE (cands E t.mem) = k) ∧
            ((sample (Spec.Dsa.decodeBE qb) d (R.drop u)).trace.head? = some 0 → d = 1))) := by
  have hRl := h.R_length
  have hq := hQ.gt
  have hdw := hQ.draw
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega_using [hd]⟩
  have hlen : (R.drop u).length = E.rl - u := by rw [List.length_drop, hRl]
  unfold draw
  refine WP.seq (WP.mono (shortTest_ok hE h h25 hu) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have h1 : SEnv E R s₁ := h.step hE k1 (o := 0) (n := 0) (by omega_using []) (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.ite (decide (E.rl - u < E.W)) ?_ (fun hs => ?_) (fun hs => ?_)
  · rw [eval_nonzero_ofNat' _ _ (by split <;> decide) a3]
    congr 1
    by_cases hc : E.rl - u < E.W <;> simp [hc]
  · simp only [decide_eq_true_eq] at hs
    refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = s₁.mem ∧ t.gpr .r31 = BitVec.ofNat 64 2)
      (by prun) (by decide)) fun t ⟨⟨tm, t31⟩, k2⟩ => ⟨h1.step hE k2 (o := 0) (n := 0) (by omega_using [])
        (by rw [tm]; exact Outside.refl _ _ _ _), by rw [tm, m1]; exact Outside.refl _ _ _ _,
        (k1.trans k2).mono (by decide), .inr ?_⟩
    have hS : sample (Spec.Dsa.decodeBE qb) (d' + 1) (R.drop u) = ⟨none, 0, [2]⟩ :=
      Dsa.Random.sample_short _ _ _ hq (by rw [hlen, hdw]; exact hs)
    rw [hS, t31, (k2.gpr .r25 (by decide)).trans ((k1.gpr .r25 (by decide)).trans h25)]
    exact ⟨rfl, rfl, (fun k hk => by cases hk), by simp⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hs
    have h25' : s₁.gpr .r25 = BitVec.ofNat 64 u := (k1.gpr .r25 (by decide)).trans h25
    refine WP.seq (WP.mono (copyRange_ok hE hQ h1 h25' (by omega_using [hu, hs])) fun s₂ ⟨⟨h2, o2, a25, a6, hc⟩, k2⟩ => ?_)
    have a17 : s₂.gpr .r17 = BitVec.ofNat 64 (d' + 1) := (k2.gpr .r17 (by decide)).trans ((k1.gpr .r17 (by decide)).trans h17)
    have hs' : drawBytes (Spec.Dsa.decodeBE qb) ≤ (R.drop u).length := by rw [hlen, hdw]; exact hs
    refine WP.mono (drawFinish_ok (a := decide (acc qb R u E.W)) a17 (by omega_using []) (by omega_using [hd'])
      (by
        rw [a6]
        by_cases ha : acc qb R u E.W
        · rw [ite_eq_left ha, ite_eq_left (show decide (acc qb R u E.W) = true from decide_eq_true ha)]
        · rw [ite_eq_right ha, ite_eq_right (show ¬ decide (acc qb R u E.W) = true by simpa using ha)]))
      fun t ⟨tm, k3, hacc, hrej⟩ => ⟨h2.step hE k3 (o := 0) (n := 0) (by omega_using []) (by rw [tm]; exact Outside.refl _ _ _ _),
        by rw [tm, ← m1]; exact o2, ((k1.trans k2).trans k3).mono (by decide), ?_⟩
    have t25 : t.gpr .r25 = BitVec.ofNat 64 (u + E.W) := (k3.gpr .r25 (by decide)).trans a25
    by_cases ha : acc qb R u E.W
    · have hS := Dsa.Random.sample_accept _ d' _ hq hs' (by rw [hdw]; exact ha)
      rw [hdw] at hS
      refine .inr ⟨?_, ?_, ?_, ?_⟩
      · rw [hacc (by simp [ha]), hS]; rfl
      · rw [t25, hS]
      · intro k hk
        rw [hS] at hk
        cases hk
        rw [tm]; exact hc
      · rw [hS]; simp
    · have hS := Dsa.Random.sample_reject _ d' _ hq hs' (by rw [hdw]; exact ha)
      rw [hdw, List.drop_drop] at hS
      obtain ⟨r17', r31z, r31k⟩ := hrej (by simp [ha])
      by_cases hd1 : d' = 0
      · subst hd1
        refine .inr ⟨?_, ?_, ?_, fun _ => rfl⟩
        · rw [r31z rfl, hS]; rfl
        · rw [t25, hS]; rfl
        · intro k hk; rw [hS] at hk; cases hk
      · refine .inl ⟨?_, by omega_using [hd1], r17', t25, by omega_using [hu, hs], ?_⟩
        · rw [r31k (by omega_using [hd1]), (k2.gpr .r31 (by decide)).trans ((k1.gpr .r31 (by decide)).trans h31)]
        · rw [hS, Nat.add_sub_cancel]

end VG.Proof.Dsa.PPC64LE.Rnd

end

end

/-!
# DSA sampling on PPC64LE: up to 128 draws

`sample_ok`: `sample`, from the octets `u` of the tape on, is
`Random.sample q 128` on the tape from `u`: it leaves its status in `r31`,
`u` plus the octets it consumed in `r25`, and an accepted candidate in the
nonce's last `W` octets; it changes memory there only.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont
open VG.Spec.Dsa.Random (sample)
open VG.Proof.Dsa.Random (sampleStatus)

theorem sampleStatus_le (S : Spec.Dsa.Random.Sample) : sampleStatus S ≤ 2 := by
  unfold sampleStatus
  split
  · decide
  · split <;> decide

theorem status_sub4 : ∀ st < 3, (BitVec.ofNat 64 st - BitVec.ofNat 64 4 == 0) = false := by decide

/-- What `sample` leaves, for `S = Random.sample q 128` from `u`. -/
structure SampleOut (E : SE) (R : List Byte) (u : Nat) (S : Spec.Dsa.Random.Sample) (s t : State) : Prop where
  env : SEnv E R t
  out : Outside E.F E.o E.W s.mem t.mem
  keep : Keep drawRegs s t
  r31 : t.gpr .r31 = BitVec.ofNat 64 (sampleStatus S)
  r25 : t.gpr .r25 = BitVec.ofNat 64 (u + S.used)
  cand : ∀ k, S.scalar = some k → Spec.Dsa.decodeBE (cands E t.mem) = k

theorem sampleLoop_ok {E : SE} {qb R : List Byte} {s₀ : State} {u₀ : Nat} {S₀ : Spec.Dsa.Random.Sample}
    (hE : E.Ok) (hQ : E.Q qb) :
    ∀ d s u, 1 ≤ d → d ≤ 128 → SEnv E R s → s.gpr .r25 = BitVec.ofNat 64 u → u ≤ E.rl →
      s.gpr .r17 = BitVec.ofNat 64 d → s.gpr .r31 = BitVec.ofNat 64 4 →
      Outside E.F E.o E.W s₀.mem s.mem → Keep drawRegs s₀ s →
      (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).scalar = S₀.scalar →
      sampleStatus (sample (Spec.Dsa.decodeBE qb) d (R.drop u)) = sampleStatus S₀ →
      u + (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).used = u₀ + S₀.used →
      WP isa (.loop (.seq draw (.block [.subi .r3 .r31 4])) (.zero .d .r3)) s (SampleOut E R u₀ S₀ s₀) := by
  intro d₀ s₁ u₁ hd₀ hd₀' h₀ h₀25 hu₀ h₀17 h₀31 ho₀ hk₀ hsc₀ hst₀ hus₀
  refine WP.loop (M := isa) (fun n (t : State) => ∃ d u, n = d ∧ 1 ≤ d ∧ d ≤ 128 ∧ SEnv E R t ∧ t.gpr .r25 = BitVec.ofNat 64 u ∧
      u ≤ E.rl ∧ t.gpr .r17 = BitVec.ofNat 64 d ∧ t.gpr .r31 = BitVec.ofNat 64 4 ∧
      Outside E.F E.o E.W s₀.mem t.mem ∧ Keep drawRegs s₀ t ∧
      (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).scalar = S₀.scalar ∧
      sampleStatus (sample (Spec.Dsa.decodeBE qb) d (R.drop u)) = sampleStatus S₀ ∧
      u + (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).used = u₀ + S₀.used) ?_ d₀ s₁
    ⟨d₀, u₁, rfl, hd₀, hd₀', h₀, h₀25, hu₀, h₀17, h₀31, ho₀, hk₀, hsc₀, hst₀, hus₀⟩
  rintro n t ⟨_, u, rfl, hd, hd', h, h25, hu, h17, h31, ho, hk, hsc, hst, hus⟩
  refine WP.seq (WP.mono (draw_ok hE hQ h h25 hu h17 hd hd' h31) fun t₁ ⟨h1, o1, k1, hc⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .r3 = t₁.gpr .r31 - BitVec.ofNat 64 4) (by prun) (by decide)) fun t₂ ⟨⟨m2, a3⟩, k2⟩ => ?_
  have h2 : SEnv E R t₂ := h1.step hE k2 (o := 0) (n := 0) (by omega_using []) (by rw [m2]; exact Outside.refl _ _ _ _)
  have o2 : Outside E.F E.o E.W s₀.mem t₂.mem := by rw [m2]; exact ho.trans o1
  have k02 : Keep drawRegs s₀ t₂ := ((hk.trans k1).trans k2).mono (by decide)
  rcases hc with ⟨b31, h2d, b17, b25, hu', hrej⟩ | ⟨b31, b25, bc, -⟩
  · refine .inr ⟨?_, n - 1, by omega_using [hd], n - 1, u + E.W, rfl, by omega_using [h2d], by omega_using [hd'], h2,
      (k2.gpr .r25 (by decide)).trans b25, hu', (k2.gpr .r17 (by decide)).trans b17,
      (k2.gpr .r31 (by decide)).trans b31, o2, k02, ?_, ?_, ?_⟩
    · rw [eval_zero, a3, b31]; rfl
    · rw [← hsc, hrej]
    · rw [← hst, hrej, Dsa.Random.sampleStatus_reject]
    · rw [← hus, hrej]; dsimp only; omega_using []
  · refine .inl ⟨?_, ⟨h2, o2, k02, ?_, ?_, ?_⟩⟩
    · rw [eval_zero, a3, b31, status_sub4 _ (by have := sampleStatus_le (sample (Spec.Dsa.decodeBE qb) n (R.drop u)); omega_using [this])]
    · rw [(k2.gpr .r31 (by decide)).trans b31, hst]
    · rw [(k2.gpr .r25 (by decide)).trans b25, hus]
    · intro k hk'
      rw [m2]
      exact bc k (hsc.trans hk')

/-- `sample`: up to 128 draws from `u`. -/
theorem sample_ok {E : SE} {qb R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h25 : s.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl) :
    WP isa Impl.Dsa.PPC64LE.Random.sample s (SampleOut E R u (sample (Spec.Dsa.decodeBE qb) 128 (R.drop u)) s) := by
  unfold Impl.Dsa.PPC64LE.Random.sample
  refine WP.seq (WP.mono (WP.keep [.r17, .r31] (Q := fun t => t.mem = s.mem ∧
    t.gpr .r17 = BitVec.ofNat 64 128 ∧ t.gpr .r31 = BitVec.ofNat 64 4) (by prun) (by decide))
    fun t ⟨⟨tm, t17, t31⟩, k⟩ => ?_)
  exact sampleLoop_ok hE hQ 128 t u (by decide) (by decide)
    (h.step hE k (o := 0) (n := 0) (by omega_using []) (by rw [tm]; exact Outside.refl _ _ _ _))
    ((k.gpr .r25 (by decide)).trans h25) hu t17 t31 (by rw [tm]; exact Outside.refl _ _ _ _) (k.mono (by decide))
    rfl rfl rfl

end VG.Proof.Dsa.PPC64LE.Rnd
