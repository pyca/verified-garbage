module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Copy
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
    rw [BitVec.toNat_or, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
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
    exact ⟨by rw [show oNonce + E.ql = E.o + E.W by simp only [SE.o]; omega], rfl⟩
  refine WP.seq (WP.mono hi fun s₁ ⟨i3, i4, i5, i6, i7, im, ird, iwr⟩ => ?_)
  have hcl : (cands E s.mem).length = E.W := VG.Proof.Bignum.bytesAt_length _ _ _
  have hql' : E.qs.length = E.W := hE.qs
  have d1 : (cands E s.mem).drop E.W = [] := List.drop_eq_nil_of_le (by omega)
  have d2 : E.qs.drop E.W = [] := List.drop_eq_nil_of_le (by omega)
  have j6 : s₁.gpr .r6 = BitVec.ofNat 64 (randomBorrow ((cands E s.mem).drop (E.W - 0)) (E.qs.drop (E.W - 0))) := by
    rw [i6, Nat.sub_zero, d1, d2]; rfl
  have j7 : s₁.gpr .r7 = randomOr ((cands E s.mem).drop (E.W - 0)) := by
    rw [i7, Nat.sub_zero, d1]; rfl
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r3 = off E.F (E.o + (E.W - i)) ∧ t.gpr .r4 = off E.qp (E.W - i) ∧
      t.gpr .r6 = BitVec.ofNat 64 (randomBorrow ((cands E s.mem).drop (E.W - i)) (E.qs.drop (E.W - i))) ∧
      t.gpr .r7 = randomOr ((cands E s.mem).drop (E.W - i)) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.seq (WP.mono (wp_countdown (body := .block (rangeByte ++ ([.subi .r5 .r5 1] : List Instr)))
    (cnt := .r5) (N := E.W) (by omega) (by omega) Inv
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
      rw [off_sub1 _ (by omega)]; congr 2; omega
    have e4 : off E.qp (E.W - i) - BitVec.ofNat 64 1 = off E.qp (E.W - i - 1) := by
      rw [off_sub1 _ (by omega)]
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
    have e1 : E.W - (i + 1) = E.W - i - 1 := by omega
    have e2 : E.W - i - 1 + 1 = E.W - i := by omega
    have hcd : (cands E s.mem).drop (E.W - i - 1) =
        (cands E s.mem).getD (E.W - i - 1) 0 :: (cands E s.mem).drop (E.W - i) := by
      rw [drop_cons_getD (by omega), e2]
    have hqd : E.qs.drop (E.W - i - 1) = E.qs.getD (E.W - i - 1) 0 :: E.qs.drop (E.W - i) := by
      rw [drop_cons_getD (by omega), e2]
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
    prun [t6, t7, nz_eq (x := (randomOr (cands E s.mem)).toNat) (by omega)]
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

end VG.Proof.Dsa.PPC64LE.Rnd
