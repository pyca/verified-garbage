module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RndEnv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomBytes
public import VerifiedGarbage.Proof.Dsa.RandomResult
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA sampling on RISC-V: a draw

As on PPC64LE (`Proof/Dsa/PPC64LE/Random/Copy.lean`, `Range.lean` and
`Draw.lean`):

* `copy_ok`: a draw of `W` octets from the tape at `used` into the nonce's
  last `W` octets, its first masked;
* `inRange_ok`: `a3 :=` 1 exactly when the nonce's last `W` octets are in
  `(0, q)`;
* `draw_ok`: a draw, against `Random.sample`: either the specification's
  sampling ends there (the status is its status), or it rejects the
  candidate and goes on with a draw fewer.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Rnd

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Bignum.RISCV64
open VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont

/-- The registers `copy` writes. -/
def copyRegs : List Reg := [.t3, .t4, .a2, .t5, .t2, .a0, .s5]

theorem copy_ok {E : SE} {R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (h : SEnv E R s)
    (h5 : s.gpr .s5 = BitVec.ofNat 64 u) (hu : u + E.W ≤ E.rl) :
    WP isa Random.copy s fun t =>
      (t.gpr .s5 = BitVec.ofNat 64 (u + E.W) ∧ Outside E.F E.o E.W s.mem t.mem ∧
        ∀ j < E.W, t.mem (off E.F (E.o + j)) = cpy (R.drop u) E.M j) ∧ Keep copyRegs s t := by
  have hf := hE.fnw
  have hW1 := hE.W1
  have hWq := hE.Wq
  have hql := hE.ql
  have hrn := hE.rnw
  have hrl := hE.rl
  have hM := hE.M
  simp only [frameBytes] at hf
  refine WP.keep copyRegs ?_ (by decide) (by rfl)
  unfold Random.copy countLoop
  have hi : WP isa (.block copyInit) s fun s₁ =>
      s₁.gpr .t3 = off E.rand u ∧ s₁.gpr .t4 = off E.F E.o ∧ s₁.gpr .t5 = BitVec.ofNat 64 E.W ∧
        s₁.gpr .t2 = BitVec.ofNat 64 E.M ∧ s₁.gpr .s5 = BitVec.ofNat 64 u ∧
        s₁.gpr .s8 = BitVec.ofNat 64 E.W ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    unfold copyInit lenQ
    brun [h.s3, h5, h.s8, h.s9, h.sp, h.lenQ hE, exec_addSp (show oNonce < 2048 by decide), BitVec.add_zero]
    show off E.F (oNonce + E.ql) - BitVec.ofNat 64 E.W = off E.F E.o
    rw [VG.Offset.add_ofNat_sub _ (by simp only [oNonce]; omega)]
    rw [show oNonce + E.ql - E.W = oNonce + (E.ql - E.W) by omega]
  refine WP.seq (WP.mono hi fun s₁ ⟨i3, i4, i5, i6, i25, i28, im, ird, iwr⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off E.rand (u + i) ∧ t.gpr .t4 = off E.F (E.o + i) ∧
      t.gpr .t2 = BitVec.ofNat 64 (if i = 0 then E.M else 255) ∧ t.gpr .s5 = BitVec.ofNat 64 u ∧
      t.gpr .s8 = BitVec.ofNat 64 E.W ∧ Outside E.F E.o E.W s.mem t.mem ∧
      (∀ j < i, t.mem (off E.F (E.o + j)) = cpy (R.drop u) E.M j) ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.seq (WP.mono (wp_countdown (body := .block (copyByte ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := E.W) (by omega) (by omega) Inv
    (fun i hi t ⟨t3, t4, t6, t25, t28, tout, tb, trd, twr⟩ _ => ?_)
    ⟨by rw [i3, Nat.add_zero], by rw [i4, Nat.add_zero], by rw [i6]; rfl, i25, i28,
      by rw [im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega), ird, iwr⟩ i5) fun t ht => ?_)
  · have hrd : InRegions (t.rd ++ t.wr) (off E.rand (u + i)) 1 := by
      rw [trd, twr]; exact h.rr _ (by omega)
    have hwr : InRegions t.wr (off E.F (E.o + i)) 1 := by
      have := (h.nw.congr twr).st (d := E.ql - E.W + i) (n := 1) (by omega)
      rwa [off_off, show oNonce + (E.ql - E.W + i) = E.o + i by simp only [SE.o]; omega] at this
    have hb : t.mem (off E.rand (u + i)) = R.getD (u + i) 0 := by
      rw [tout _ (outside_of_disj hE hE.dR (VG.Offset.contains_base _ (by omega) (by omega)) (o := E.ql - E.W)
        (n := E.W) (by omega)), h.byte (by omega)]
    generalize hv : (BitVec.ofNat 64 (t.mem (off E.rand (u + i))).toNat &&&
      BitVec.ofNat 64 (if i = 0 then E.M else 255)).setWidth 8 = v
    have hst : WP isa (.block (copyByte ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
        t'.gpr .t3 = off E.rand (u + i + 1) ∧ t'.gpr .t4 = off E.F (E.o + i + 1) ∧
          t'.gpr .t2 = BitVec.ofNat 64 255 ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
          t'.gpr .s5 = t.gpr .s5 ∧ t'.gpr .s8 = t.gpr .s8 ∧
          t'.mem = t.mem.write (off E.F (E.o + i)) 1 v ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
      unfold copyByte
      brun [t3, t4, t6, hrd, hwr, BitVec.add_zero, read_byte64, hv, exec_li_lit (show 255 < 2048 by decide)]
    have hw1 := write1_outside t.mem E.F (d := E.o + i) v (by simp only [SE.o, oNonce]; omega)
    refine WP.mono hst fun t' ⟨a3, a4, a6, a5, a25, a28, am, ard, awr⟩ => ⟨⟨by rw [a3, Nat.add_assoc],
      by rw [a4, Nat.add_assoc], ?_, a25.trans t25, a28.trans t28, ?_, ?_, ard.trans trd, awr.trans twr⟩, a5⟩
    · rw [a6, ite_eq_right (by omega)]
    · rw [am]; exact tout.trans (hw1.mono (by omega) (by omega))
    · intro j hj
      rw [am]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [hw1 _ (by rw [Mont.ofs_off0 E.F (by simp only [SE.o, oNonce]; omega)]; omega)]; exact tb j hj
      · have hd : ∀ k, (R.drop u).getD k 0 = R.getD (u + k) 0 := fun k => by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        rw [write1_self, ← hv, hb, cpy, hd, hd]
        split
        · rename_i hj0; subst hj0
          exact mask_byte _ hM
        · exact mask_byte_ff _
  · obtain ⟨-, -, -, t25, t28, tout, tb, -, -⟩ := ht
    brun [t25, t28, BitVec.ofNat_add_ofNat]
    exact ⟨tout, tb⟩

/-! ## The candidate's test -/

/-- The registers `inRange` writes. -/
def rangeRegs : List Reg := [.t3, .a2, .t4, .t5, .a3, .a4, .a0, .a5]

/-- The candidate: the nonce's last `W` octets. -/
abbrev cands (E : SE) (m : Mem) : List Byte := Spec.Rsa.bytesAt m (off E.F E.o) E.W

theorem randomOr_lt : ∀ bs : List Byte, (randomOr bs).toNat < 256
  | [] => by decide
  | b :: bs => by
    show (randomOr bs ||| b.setWidth 64).toNat < 256
    rw [BitVec.toNat_or, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
    exact or_lt (randomOr_lt bs) b.isLt

theorem setWidth_byte (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem drop_cons_getD {bs : List Byte} {k : Nat} (hk : k < bs.length) :
    bs.drop k = bs.getD k 0 :: bs.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl

theorem inRange_ok {E : SE} {R : List Byte} {s : State} (hE : E.Ok) (h : SEnv E R s) :
    WP isa Random.inRange s fun t =>
      (t.gpr .a3 = BitVec.ofNat 64 (if 0 < Spec.Dsa.decodeBE (cands E s.mem) ∧
          Spec.Dsa.decodeBE (cands E s.mem) < Spec.Dsa.decodeBE E.qs then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep rangeRegs s t := by
  have hf := hE.fnw
  have hW1 := hE.W1
  have hWq := hE.Wq
  have hql := hE.ql
  have hqn := hE.qnw
  simp only [frameBytes] at hf
  refine WP.keep rangeRegs ?_ (by decide) (by rfl)
  unfold Random.inRange countLoop
  have hi : WP isa (.block rangeInit) s fun s₁ =>
      s₁.gpr .t3 = off E.F (E.o + E.W) ∧ s₁.gpr .t4 = off E.qp E.W ∧ s₁.gpr .t5 = BitVec.ofNat 64 E.W ∧
        s₁.gpr .a3 = BitVec.ofNat 64 0 ∧ s₁.gpr .a4 = 0 ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    unfold rangeInit lenQ
    brun [h.s7, h.s8, h.sp, h.lenQ hE, exec_addSp (show oNonce < 2048 by decide), exec_li_zero, BitVec.add_zero]
    exact ⟨by rw [show oNonce + E.ql = E.o + E.W by simp only [SE.o]; omega], rfl⟩
  refine WP.seq (WP.mono hi fun s₁ ⟨i3, i4, i5, i6, i7, im, ird, iwr⟩ => ?_)
  have hcl : (cands E s.mem).length = E.W := VG.Proof.Bignum.bytesAt_length _ _ _
  have hql' : E.qs.length = E.W := hE.qs
  have d1 : (cands E s.mem).drop E.W = [] := List.drop_eq_nil_of_le (by omega)
  have d2 : E.qs.drop E.W = [] := List.drop_eq_nil_of_le (by omega)
  have j6 : s₁.gpr .a3 = BitVec.ofNat 64 (randomBorrow ((cands E s.mem).drop (E.W - 0)) (E.qs.drop (E.W - 0))) := by
    rw [i6, Nat.sub_zero, d1, d2]; rfl
  have j7 : s₁.gpr .a4 = randomOr ((cands E s.mem).drop (E.W - 0)) := by
    rw [i7, Nat.sub_zero, d1]; rfl
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off E.F (E.o + (E.W - i)) ∧ t.gpr .t4 = off E.qp (E.W - i) ∧
      t.gpr .a3 = BitVec.ofNat 64 (randomBorrow ((cands E s.mem).drop (E.W - i)) (E.qs.drop (E.W - i))) ∧
      t.gpr .a4 = randomOr ((cands E s.mem).drop (E.W - i)) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.seq (WP.mono (wp_countdown (body := .block (rangeByte ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := E.W) (by omega) (by omega) Inv
    (fun i hi t ⟨t3, t4, t6, t7, tm, trd, twr⟩ _ => ?_)
    ⟨by rw [i3, Nat.sub_zero], by rw [i4, Nat.sub_zero], j6, j7, im, ird, iwr⟩ i5)
    fun t ht => ?_)
  · have k1 : E.W - i - 1 < E.W := by omega
    have hrd3 : InRegions (t.rd ++ t.wr) (off E.F (E.o + (E.W - i - 1))) 1 := by
      have := (h.nw.congr twr).ld (d := E.ql - E.W + (E.W - i - 1)) (n := 1) (by omega)
      rw [off_off, show oNonce + (E.ql - E.W + (E.W - i - 1)) = E.o + (E.W - i - 1) by simp only [SE.o]; omega] at this
      exact this
    have hrd4 : InRegions (t.rd ++ t.wr) (off E.qp (E.W - i - 1)) 1 := by
      rw [trd, twr]; exact h.qr _ k1
    have e3 : off E.F (E.o + (E.W - i)) - BitVec.ofNat 64 1 = off E.F (E.o + (E.W - i - 1)) := by
      rw [VG.Offset.add_ofNat_sub _ (by omega)]; congr 2; omega
    have e4 : off E.qp (E.W - i) - BitVec.ofNat 64 1 = off E.qp (E.W - i - 1) := by
      rw [VG.Offset.add_ofNat_sub _ (by omega)]
    have hc : t.mem (off E.F (E.o + (E.W - i - 1))) = (cands E s.mem).getD (E.W - i - 1) 0 := by
      rw [tm]; simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, k1, off_add]
    have hq : t.mem (off E.qp (E.W - i - 1)) = E.qs.getD (E.W - i - 1) 0 := by
      rw [tm]; exact h.qbyte k1
    have hb := Dsa.randomBorrow_le ((cands E s.mem).drop (E.W - i)) (E.qs.drop (E.W - i))
    have hcb := ((cands E s.mem).getD (E.W - i - 1) 0).isLt
    have hqb := (E.qs.getD (E.W - i - 1) 0).isLt
    unfold rangeByte
    brun [t3, t4, t6, t7, e3, e4, hrd3, hrd4, BitVec.add_zero, read_byte64, hc, hq, borrow_eq hcb hqb hb]
    have e1 : E.W - (i + 1) = E.W - i - 1 := by omega
    have e2 : E.W - i - 1 + 1 = E.W - i := by omega
    have hcd : (cands E s.mem).drop (E.W - i - 1) =
        (cands E s.mem).getD (E.W - i - 1) 0 :: (cands E s.mem).drop (E.W - i) := by
      rw [drop_cons_getD (by omega), e2]
    have hqd : E.qs.drop (E.W - i - 1) = E.qs.getD (E.W - i - 1) 0 :: E.qs.drop (E.W - i) := by
      rw [drop_cons_getD (by omega), e2]
    refine ⟨by gsimp; rw [e1], by gsimp; rw [e1], ?_, ?_, by gsimp; exact tm, by gsimp; exact trd,
      by gsimp; exact twr⟩
    · gsimp
      (rw [e1, hcd, hqd]) <;> rfl
    · gsimp
      (rw [e1, hcd, ← setWidth_byte]) <;> rfl
  · obtain ⟨-, -, t6, t7, tm, -, -⟩ := ht
    simp only [Nat.sub_self, List.drop_zero] at t6 t7
    have hor := randomOr_lt (cands E s.mem)
    unfold rangeFinish
    rw [← VG.Proof.Bignum.ofNat_toNat64 (randomOr (cands E s.mem))] at t7
    brun [t6, t7, exec_li_zero]
    rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, nz_eq (x := (randomOr (cands E s.mem)).toNat) (by omega)]
    refine ⟨?_, tm⟩
    rw [Dsa.randomBorrow_eq _ _ (by rw [hcl, hql'])]
    have hz := Dsa.randomOr_zero (cands E s.mem)
    have hz' : (randomOr (cands E s.mem)).toNat = 0 ↔ Spec.Dsa.decodeBE (cands E s.mem) = 0 := by
      rw [← hz]
      exact ⟨fun e => BitVec.eq_of_toNat_eq e, fun e => by rw [e]; rfl⟩
    by_cases h1 : Spec.Dsa.decodeBE (cands E s.mem) = 0
    · rw [ite_eq_left (hz'.mpr h1), ite_eq_right (show ¬ (0 < Spec.Dsa.decodeBE (cands E s.mem) ∧ _) by omega)]
      split <;> rfl
    · rw [ite_eq_right (fun e => h1 (hz'.mp e))]
      by_cases h2 : Spec.Dsa.decodeBE (cands E s.mem) < Spec.Dsa.decodeBE E.qs
      · rw [ite_eq_left h2, ite_eq_left ⟨by omega, h2⟩]; rfl
      · rw [ite_eq_right h2, ite_eq_right (fun h => h2 h.2)]; rfl

/-! ## A draw -/

theorem shortTest_ok {E : SE} {R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (h : SEnv E R s)
    (h5 : s.gpr .s5 = BitVec.ofNat 64 u) (hu : u ≤ E.rl) :
    WP isa (.block shortTest) s fun t =>
      (t.gpr .a0 = BitVec.ofNat 64 (if E.rl - u < E.W then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.a0, .a1] s t := by
  have hrn := hE.rl
  have hW := hE.Wq
  have hql := hE.ql
  refine WP.keep _ ?_ (by decide) (by rfl)
  unfold shortTest
  brun [h.s4, h5, h.s8, VG.Offset.ofNat_sub_ofNat hu]
  exact short_eq (x := E.rl - u) (w := E.W) (by omega) (by omega)

/-- What `drawFinish` decides. -/
theorem drawFinish_ok {s : State} {d : Nat} {a : Bool} (h11 : s.gpr .s11 = BitVec.ofNat 64 d) (hd : 1 ≤ d)
    (hd' : d < 2 ^ 64) (h3 : s.gpr .a3 = BitVec.ofNat 64 (if a then 1 else 0)) :
    WP isa drawFinish s fun t =>
      t.mem = s.mem ∧ Keep [.s11, .s10] s t ∧ (a = true → t.gpr .s10 = BitVec.ofNat 64 1) ∧
        (a = false → t.gpr .s11 = BitVec.ofNat 64 (d - 1) ∧ (d = 1 → t.gpr .s10 = BitVec.ofNat 64 0) ∧
          (d ≠ 1 → t.gpr .s10 = s.gpr .s10)) := by
  unfold drawFinish
  refine WP.ite (a == true) ?_ (fun ha => ?_) (fun ha => ?_)
  · rw [Steps.eval_nonzero, h3]; cases a <;> rfl
  · simp only [beq_iff_eq] at ha
    refine WP.mono (WP.keep [.s11, .s10] (Q := fun t => t.mem = s.mem ∧ t.gpr .s10 = BitVec.ofNat 64 1)
      (by brun [exec_li_lit (show 1 < 2048 by decide)]) (by decide) (by rfl))
      fun t ⟨⟨tm, t31⟩, k⟩ => ⟨tm, k, fun _ => t31, fun h => by rw [ha] at h; cases h⟩
  · have ha' : a = false := by cases a <;> simp_all
    subst ha'
    refine WP.seq (WP.mono (WP.keep [.s11] (Q := fun t => t.mem = s.mem ∧
      t.gpr .s11 = BitVec.ofNat 64 (d - 1)) (by brun [h11, VG.Offset.ofNat_sub_ofNat hd]) (by decide) (by rfl))
      fun t₁ ⟨⟨m1, a17⟩, k1⟩ => ?_)
    refine WP.ite (decide (d - 1 = 0)) (Steps.eval_zero_ofNat _ _ (by omega) a17) (fun hz => ?_) (fun hz => ?_)
    · simp only [decide_eq_true_eq] at hz
      refine WP.mono (WP.keep [.s10] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .s10 = BitVec.ofNat 64 0)
        (by brun [exec_li_zero]; rfl) (by decide) (by rfl)) fun t ⟨⟨tm, t31⟩, k⟩ => ⟨tm.trans m1, (k1.trans k).mono (by decide),
          (fun h => by cases h), fun _ => ⟨(k.gpr (by decide)).trans a17, fun _ => t31,
            fun h => absurd (by omega) h⟩⟩
    · simp only [decide_eq_false_iff_not] at hz
      refine WP.mono (WP.block_nil rfl) fun t ht => ?_
      subst ht
      exact ⟨m1, k1.mono (by decide), (fun h => by cases h), fun _ => ⟨a17, fun h => absurd (by omega) hz,
        fun _ => k1.gpr (by decide)⟩⟩

open VG.Spec.Dsa.Random (sample candidate drawBytes)
open VG.Proof.Dsa.Random (sampleStatus)

/-- Whether the draw at `u` is accepted. -/
abbrev acc (qb R : List Byte) (u W : Nat) : Prop :=
  0 < candidate (Spec.Dsa.decodeBE qb) ((R.drop u).take W) ∧
    candidate (Spec.Dsa.decodeBE qb) ((R.drop u).take W) < Spec.Dsa.decodeBE qb

/-- `copy` then `inRange`: the candidate in the nonce, and whether it is accepted. -/
theorem copyRange_ok {E : SE} {qb R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h5 : s.gpr .s5 = BitVec.ofNat 64 u) (hu : u + E.W ≤ E.rl) :
    WP isa (.seq Random.copy Random.inRange) s fun t =>
      (SEnv E R t ∧ Outside E.F E.o E.W s.mem t.mem ∧ t.gpr .s5 = BitVec.ofNat 64 (u + E.W) ∧
        t.gpr .a3 = BitVec.ofNat 64 (if acc qb R u E.W then 1 else 0) ∧
        Spec.Dsa.decodeBE (cands E t.mem) = candidate (Spec.Dsa.decodeBE qb) ((R.drop u).take E.W)) ∧
      Keep (copyRegs ++ rangeRegs) s t := by
  have hRl := h.R_length
  refine WP.seq (WP.mono (wp_sp (copy_ok hE h h5 hu)) fun s₁ ⟨⟨⟨a25, o1, cb⟩, k1⟩, sp1⟩ => ?_)
  have h1 : SEnv E R s₁ :=
    h.step hE k1 sp1 (o := E.ql - E.W) (n := E.W) (by have := hE.ql; have := hE.Wq; omega) o1
  have hc : cands E s₁.mem = cpyList (R.drop u) E.M E.W := by
    apply List.ext_getElem
    · simp [cands, VG.Proof.Bignum.bytesAt_length]
    · intro j hj _
      simp only [cands, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, cpyList]
      rw [← cb j (by simpa [VG.Proof.Bignum.bytesAt_length] using hj), off_add]
  have hcand : Spec.Dsa.decodeBE (cands E s₁.mem) = candidate (Spec.Dsa.decodeBE qb) ((R.drop u).take E.W) := by
    rw [hc, hQ.cand (by rw [List.length_drop]; omega)]
  refine WP.mono (wp_sp (inRange_ok hE h1)) fun t ⟨⟨⟨a6, tm⟩, k2⟩, sp2⟩ =>
    ⟨⟨h1.stepM hE k2 sp2 tm, ?_, ?_, ?_, ?_⟩, k1.trans k2⟩
  · rw [tm]; exact o1
  · rw [k2.gpr (by decide)]; exact a25
  · rw [a6, hcand, hQ.qs_val]
  · rw [tm]; exact hcand

/-- The registers a draw writes. -/
def drawRegs : List Reg := [.a0, .a1, .t3, .t4, .a2, .t5, .t2, .s5, .a3, .a4, .a5, .s11, .s10]

/-- A rejected draw of `W` octets, then `S`. -/
abbrev rejectOf (W : Nat) (S : Spec.Dsa.Random.Sample) : Spec.Dsa.Random.Sample :=
  { S with used := W + S.used, trace := 0 :: S.trace }

theorem draw_ok {E : SE} {qb R : List Byte} {s : State} {u d : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h5 : s.gpr .s5 = BitVec.ofNat 64 u) (hu : u ≤ E.rl)
    (h11 : s.gpr .s11 = BitVec.ofNat 64 d) (hd : 1 ≤ d) (hd' : d ≤ 128) (h10 : s.gpr .s10 = BitVec.ofNat 64 4) :
    WP isa draw s fun t =>
      SEnv E R t ∧ Outside E.F E.o E.W s.mem t.mem ∧ Keep drawRegs s t ∧
        ((t.gpr .s10 = BitVec.ofNat 64 4 ∧ 2 ≤ d ∧ t.gpr .s11 = BitVec.ofNat 64 (d - 1) ∧
            t.gpr .s5 = BitVec.ofNat 64 (u + E.W) ∧ u + E.W ≤ E.rl ∧
            sample (Spec.Dsa.decodeBE qb) d (R.drop u) =
              rejectOf E.W (sample (Spec.Dsa.decodeBE qb) (d - 1) (R.drop (u + E.W)))) ∨
          (t.gpr .s10 = BitVec.ofNat 64 (sampleStatus (sample (Spec.Dsa.decodeBE qb) d (R.drop u))) ∧
            t.gpr .s5 = BitVec.ofNat 64 (u + (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).used) ∧
            (∀ k, (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).scalar = some k →
              Spec.Dsa.decodeBE (cands E t.mem) = k) ∧
            ((sample (Spec.Dsa.decodeBE qb) d (R.drop u)).trace.head? = some 0 → d = 1))) := by
  have hRl := h.R_length
  have hq := hQ.gt
  have hdw := hQ.draw
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hlen : (R.drop u).length = E.rl - u := by rw [List.length_drop, hRl]
  unfold draw
  refine WP.seq (WP.mono (wp_sp (shortTest_ok hE h h5 hu)) fun s₁ ⟨⟨⟨a3, m1⟩, k1⟩, sp1⟩ => ?_)
  have h1 : SEnv E R s₁ := h.stepM hE k1 sp1 m1
  refine WP.ite (decide (E.rl - u < E.W)) ?_ (fun hs => ?_) (fun hs => ?_)
  · rw [Steps.eval_nonzero_ofNat _ _ (by split <;> decide) a3]
    congr 1
    by_cases hc : E.rl - u < E.W <;> simp [hc]
  · simp only [decide_eq_true_eq] at hs
    refine WP.mono (wp_sp (WP.keep [.s10] (Q := fun t => t.mem = s₁.mem ∧ t.gpr .s10 = BitVec.ofNat 64 2)
      (by brun [exec_li_lit (show 2 < 2048 by decide)]) (by decide) (by rfl)))
      fun t ⟨⟨⟨tm, t31⟩, k2⟩, sp2⟩ => ⟨h1.stepM hE k2 sp2 tm, by rw [tm, m1]; exact Outside.refl _ _ _ _,
        (k1.trans k2).mono (by decide), .inr ?_⟩
    have hS : sample (Spec.Dsa.decodeBE qb) (d' + 1) (R.drop u) = ⟨none, 0, [2]⟩ :=
      Dsa.Random.sample_short _ _ _ hq (by rw [hlen, hdw]; exact hs)
    rw [hS, t31, (k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans h5)]
    exact ⟨rfl, rfl, (fun k hk => by cases hk), by simp⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hs
    have h5' : s₁.gpr .s5 = BitVec.ofNat 64 u := (k1.gpr (by decide)).trans h5
    refine WP.seq (WP.mono (wp_sp (copyRange_ok hE hQ h1 h5' (by omega)))
      fun s₂ ⟨⟨⟨h2, o2, a25, a6, hc⟩, k2⟩, _⟩ => ?_)
    have a17 : s₂.gpr .s11 = BitVec.ofNat 64 (d' + 1) := (k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans h11)
    have hs' : drawBytes (Spec.Dsa.decodeBE qb) ≤ (R.drop u).length := by rw [hlen, hdw]; exact hs
    refine WP.mono (wp_sp (drawFinish_ok (a := decide (acc qb R u E.W)) a17 (by omega) (by omega)
      (by
        rw [a6]
        by_cases ha : acc qb R u E.W
        · rw [ite_eq_left ha, ite_eq_left (show decide (acc qb R u E.W) = true from decide_eq_true ha)]
        · rw [ite_eq_right ha, ite_eq_right (show ¬ decide (acc qb R u E.W) = true by simpa using ha)])))
      fun t ⟨⟨tm, k3, hacc, hrej⟩, sp3⟩ => ⟨h2.stepM hE k3 sp3 tm, by rw [tm, ← m1]; exact o2,
        ((k1.trans k2).trans k3).mono (by decide), ?_⟩
    have t25 : t.gpr .s5 = BitVec.ofNat 64 (u + E.W) := (k3.gpr (by decide)).trans a25
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
      · refine .inl ⟨?_, by omega, r17', t25, by omega, ?_⟩
        · rw [r31k (by omega), (k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans h10)]
        · rw [hS, Nat.add_sub_cancel]

end VG.Proof.Dsa.RISCV64.Rnd
