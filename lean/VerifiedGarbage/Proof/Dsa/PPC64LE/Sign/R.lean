module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Gk
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.KeyPair
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Spec.RsaPss

/-!
# DSA signing on PPC64LE: r and the masks of the ranges

* `nonZero_ok`: `r22 &=` the mask of `[a] ≠ 0`, with 0 in array 7;
* `rRanges_ok`: in the Q space, `r = (g^k mod p) mod q` (`reduce` of the
  buffer's `p_len` octets) into array 9, and the header's word `hMask &=` the
  masks of `0 < k < q`, `0 < x < q` and `r ≠ 0`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot slot_sep)

/-- The registers `nonZero` writes. -/
def nonZeroRegs : List Reg := [.r20] ++ eqRegs .r19 ++ [.r20, .r22]

/-- `nonZero a`: `r22 &=` the mask of `[a] ≠ 0`, with 0 in array 7. -/
theorem nonZero_ok {s : State} {B : Addr} {Z w a : Nat} {b : Bool} (h : Env s B Z w) (ha : a < 28)
    (h7 : arr s.mem B w 7 = 0) (h22 : s.gpr .r22 = mask b) :
    WP isa (nonZero a) s fun t =>
      (t.gpr .r22 = mask (b && decide (arr s.mem B w a ≠ 0)) ∧ t.mem = s.mem) ∧ Keep nonZeroRegs s t := by
  unfold nonZero
  refine WP.seq (WP.mono (ones_ok s) fun s₁ ⟨⟨a20, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (eqMask_ok (h.keep k1 (by decide)) .r19 (a := a) (b := 7) ha (by decide))
    fun s₂ ⟨⟨a19, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.r20, .r22] (Q := fun t => t.gpr .r22 = mask (b && decide (arr s.mem B w a ≠ 0)) ∧
      t.mem = s₂.mem) ?_ (by decide)) fun t ⟨⟨t22, tm⟩, kt⟩ => ⟨⟨t22, by rw [tm, m2, m1]⟩, (k12.trans kt).mono (by decide)⟩
  have b20 : s₂.gpr .r20 = mask true := (k2.gpr .r20 (by decide)).trans a20
  have b22 : s₂.gpr .r22 = mask b := (k12.gpr .r22 (by decide)).trans h22
  rw [m1, ← arr, ← arr, h7] at a19
  unfold clear19
  prun [b20, b22, a19, mask_clear, mask_and]
  simp only [Bool.true_and, decide_not]

/-- The registers `rRanges` writes. -/
def rRangesRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r19, .r20, .r22, .r23, .r24,
    .r25, .r29, .r30, .r31]

/-- `rRanges`: in the Q space, r into array 9, and `hMask &=` the masks of
`0 < k < q`, `0 < x < q` and `r ≠ 0`. Memory changes only in the Q space's
arrays 1–9 and in `hMask`. -/
theorem rRanges_ok {s : State} {L : Lay} {key nonce dig : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key nonce dig) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hq : 0 < arrQ s.mem L 0) (hm : word s.mem L.S hMask = mask b) :
    WP isa rRanges s fun t =>
      (QS t L key nonce dig ∧
        arrQ t.mem L 9 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 ∧
        word t.mem L.S hMask = mask (b && decide ((0 < kOf s.mem L nonce ∧ kOf s.mem L nonce < arrQ s.mem L 0) ∧
          (0 < xOf s.mem L key ∧ xOf s.mem L key < arrQ s.mem L 0) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 ≠ 0)) ∧
        (∃ m, Outside L.Q (slot 4 1) (slot 4 10 - slot 4 1) s.mem m ∧ Outside L.S hMask 8 m t.mem)) ∧
        Keep rRangesRegs s t := by
  have hql := hL.ql
  have hpl := hL.pl
  have hZ := hL.z256
  have hnw : slot 4 28 ≤ 2 ^ 64 := by decide
  have e71 : slot 4 1 = 304 := rfl
  unfold rRanges
  -- r into array 1.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  refine WP.mono (bufBase_ok hL (hr.keep k1) (rd := .r30) (t := .r0) (by decide)) fun s₁' ⟨⟨a30, m1'⟩, k1'⟩ => ?_
  refine WP.mono (getP_ok ((hr.keep k1).keep k1') .r31) fun s₂ ⟨⟨a31, m2⟩, k2'⟩ => ?_
  have k2 := k1'.trans k2'
  replace a30 : s₂.gpr .r30 = L.Buf := (k2'.gpr .r30 (by decide)).trans a30
  replace m2 : s₂.mem = s₁.mem := m2.trans m1'
  have k12 := k1.trans k2
  have m21 : s₂.mem = s.mem := m2.trans m1
  have e2 := q1.env
  refine WP.seq (WP.mono (ModArith.reduce_ok (B := L.Q) (Z := 1600) (w := 4) (D := L.Buf) (L := L.pl)
    (e2.hs.congr k2.wr) (by decide) (by decide)
    (by decide) ((k2.gpr .r10 (by decide)).trans e2.h10) ((k2.gpr .r29 (by decide)).trans e2.h29)
    ((k2.gpr .r11 (by decide)).trans e2.h11) (by rw [m2]; exact (show 0 < arr s₁.mem L.Q 4 0 by rw [m1]; exact hq))
    (by rw [a30]; exact (BitVec.add_zero _).symm) a31 (by omega) (by omega)
    (fun i hi => by
      rw [k12.rd, k12.wr]
      exact (ScrL.bufN hs hL (n := L.pl) (by omega)).ld (show i + 1 ≤ L.pl by omega))
    (buf_apartQ L (by omega))) fun s₃ ⟨⟨v1, o3⟩, k3⟩ => ?_)
  rw [m21] at v1
  have k13 := k12.trans k3
  have o3' : Outside L.Q (slot 4 1) (24 * (4 + 2)) s.mem s₃.mem := by rw [← m21]; exact o3
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₃.mem)
      (by prun [((k2.trans k3).gpr .r23 (by decide)).trans q1.h23, BitVec.add_zero]) (by decide))
    fun s₄ ⟨⟨a31', m4⟩, k4⟩ => ?_)
  have q4 : InQ s₄ L := ⟨⟨e2.hs.congr (k2.trans (k3.trans k4)).wr,
    ((k3.trans k4).gpr .r10 (by decide)).trans ((k2.gpr .r10 (by decide)).trans e2.h10),
    ((k2.trans (k3.trans k4)).gpr .r29 (by decide)).trans e2.h29,
    ((k2.trans (k3.trans k4)).gpr .r11 (by decide)).trans e2.h11, a31', by decide, by decide, by decide⟩,
    ((k2.trans (k3.trans k4)).gpr .r21 (by decide)).trans q1.h21,
    ((k2.trans (k3.trans k4)).gpr .r23 (by decide)).trans q1.h23⟩
  have k14 := k13.trans k4
  have Q4 : QS s₄ L key nonce dig := ⟨q4, hs.congr k14.wr, hr.keep k14⟩
  -- r into array 9, 0 into array 7.
  refine WP.seq (WP.mono (copy_ok Q4.inq.env (o := 9) (a := 1) (by decide) (by decide) (by decide))
    fun s₅ ⟨⟨v9, o5⟩, k5⟩ => ?_)
  have Q5 := Q4.step k5 (by decide)
  refine WP.seq (WP.mono (zeroArr_ok Q5.inq.env (j := 7) (by decide)) fun s₆ ⟨⟨z7, o6⟩, k6⟩ => ?_)
  have Q6 := Q5.step k6 (by decide)
  have k16 := (k14.trans k5).trans k6
  -- k into array 6, x into array 5.
  refine WP.seq (WP.mono (ptrR_ok Q6.regs) fun s₇ ⟨⟨b12, b6, m7⟩, k7⟩ => ?_)
  have Q7 := Q6.step k7 (by decide)
  have k17 := k16.trans k7
  refine WP.seq (WP.mono (loadQ_ok (j := 6) Q7 hL (by decide) (by decide) (hn.keep k17.rd k17.wr) b12 b6
      (by omega) (by omega)) fun s₈ ⟨⟨Q8, v6, top6, o8, qa8⟩, k8⟩ => ?_)
  refine WP.seq (WP.mono (ptrX_ok Q8.regs) fun s₉ ⟨⟨c12, c6, m9⟩, k9⟩ => ?_)
  have Q9 := Q8.step k9 (by decide)
  have k19 := (k17.trans k8).trans k9
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q9 hL (by decide) (by decide)
      ((hk.keep k19.rd k19.wr).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)) c12 c6
      (by omega) (by omega)) fun s₁₀ ⟨⟨Q10, v5, top5, o10, qa10⟩, k10⟩ => ?_)
  have k110 := k19.trans k10
  have ae : ∀ {m m' : Mem} {o n : Nat}, Outside L.Q (slot 4 o) n m m' → n ≤ 48 → ∀ j, j < 28 → j ≠ o →
      arr m' L.Q 4 j = arr m L.Q 4 j := fun h hn' j hj ho =>
    Outside.arrEq (h.mono (Nat.le_refl _) (by omega)) hj ho hnw
  have qa3 : QArr L s.mem s₃.mem := QArr.of o3' (Nat.le_refl _) (by rw [e71]; decide)
  have qa7 : QArr L s.mem s₇.mem := by
    rw [m7, ← m4] at *
    exact (qa3.trans (QArr.of o5 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega))).trans
      (QArr.of o6 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega))
  have qa9 : QArr L s.mem s₉.mem := by rw [m9]; exact qa7.trans qa8
  have qa10' : QArr L s.mem s₁₀.mem := qa9.trans qa10
  -- `hMask` into `r22`.
  have h21 : s₁₀.gpr .r21 = L.S := Q10.regs.r21
  have hld : InRegions (s₁₀.rd ++ s₁₀.wr) (s₁₀.gpr .r21 + BitVec.ofNat 64 hMask) 8 := by
    rw [h21]; exact Q10.scr.ld (show hMask + 8 ≤ L.Z by simp only [hMask]; omega)
  have hw10 : word s₁₀.mem L.S hMask = mask b := by
    rw [Outside.word (qa10'.qbody.body hL) (Or.inl (by simp only [hMask]; omega)) (by simp only [hMask]; omega)]
    exact hm
  refine WP.seq (WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = mask b ∧ u.mem = s₁₀.mem)
    (by prun [exec_ld (by decide) hld]; rw [h21, ← hw10]) (by decide)) fun s₁₁ ⟨⟨a22, m11⟩, k11⟩ => ?_)
  have Q11 := Q10.step k11 (by decide)
  -- The values in arrays 0, 5, 6 and 9.
  have A0 : arr s₁₁.mem L.Q 4 0 = arrQ s.mem L 0 := by rw [m11]; exact qa10'.arr0
  have A6 : arr s₁₁.mem L.Q 4 6 = kOf s.mem L nonce := by
    rw [m11, ae o10 (by omega) 6 (by decide) (by decide), m9]
    refine v6.trans ?_
    rw [kOf, hn.bytes (qa7.qbody.body hL) hZ]
  have A5 : arr s₁₁.mem L.Q 4 5 = xOf s.mem L key := by
    rw [m11]
    refine v5.trans ?_
    rw [xOf, (hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)).bytes (qa9.qbody.body hL) hZ]
  have A9 : arr s₁₁.mem L.Q 4 9 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 := by
    rw [m11, ae o10 (by omega) 9 (by decide) (by decide), m9, ae o8 (by omega) 9 (by decide) (by decide), m7,
      ae o6 (by omega) 9 (by decide) (by decide), v9, m4]
    exact v1
  have z7' : arr s₁₁.mem L.Q 4 7 = 0 := by
    rw [m11, ae o10 (by omega) 7 (by decide) (by decide), m9, ae o8 (by omega) 7 (by decide) (by decide), m7]
    exact z7
  have top6' : word s₁₁.mem L.Q (slot 4 6 + 8 * 4) = 0 := by
    rw [m11, Outside.word o10 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega), m9]; exact top6
  -- The ranges and `r ≠ 0`.
  refine WP.seq (WP.mono (inRange_ok Q11.inq.env (a := 6) (b := b) (by decide) (by decide) top6' z7' a22)
    fun s₁₂ ⟨⟨b22, o12⟩, k12'⟩ => ?_)
  have Q12 := Q11.step k12' (by decide)
  have top5' : word s₁₂.mem L.Q (slot 4 5 + 8 * 4) = 0 := by
    rw [Outside.word o12 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega), m11]; exact top5
  refine WP.seq (WP.mono (inRange_ok Q12.inq.env (a := 5) (b := _) (by decide) (by decide) top5'
    (by rw [ae o12 (by omega) 7 (by decide) (by decide)]; exact z7') b22) fun s₁₃ ⟨⟨c22, o13⟩, k13'⟩ => ?_)
  have Q13 := Q12.step k13' (by decide)
  refine WP.seq (WP.mono (nonZero_ok Q13.inq.env (a := 9) (by decide)
    (by rw [ae o13 (by omega) 7 (by decide) (by decide), ae o12 (by omega) 7 (by decide) (by decide)]; exact z7')
    c22) fun s₁₄ ⟨⟨d22, m14⟩, k14'⟩ => ?_)
  have Q14 := Q13.step k14' (by decide)
  -- The mask to `hMask`.
  have h21' : s₁₄.gpr .r21 = L.S := Q14.regs.r21
  have hst : InRegions s₁₄.wr (L.S + BitVec.ofNat 64 hMask) 8 := Q14.scr.st (by simp only [hMask]; omega)
  have he : exec (.store .d .r22 .r21 hMask) s₁₄ =
      some { s₁₄ with mem := s₁₄.mem.writeW (L.S + BitVec.ofNat 64 hMask) (s₁₄.gpr .r22) } := by
    rw [exec_std (by decide) (by rw [h21']; exact hst), h21']
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s₁₄.mem.writeW (L.S + BitVec.ofNat 64 hMask) (s₁₄.gpr .r22))
    (by prun [he]) (by decide)) fun t ⟨mt, kt⟩ => ?_
  have wo : Outside L.S hMask 8 s₁₄.mem t.mem := by
    rw [mt]; exact writeW_outside s₁₄.mem L.S (d := hMask) _ (by simp only [hMask]; omega)
  have wq : ∀ j, j < 28 → arr t.mem L.Q 4 j = arr s₁₄.mem L.Q 4 j := fun j hj =>
    Outside.val32 (mask_keepQ hL wo) (Or.inl (by simp only [slot_eq]; omega)) (by simp only [slot_eq]; omega)
  have kall := ((((k110.trans k11).trans k12').trans k13').trans k14').trans kt
  have mo : ∀ {m m' : Mem} {o n : Nat}, Outside L.Q (slot 4 o) n m m' → 1 ≤ o → slot 4 o + n ≤ slot 4 10 →
      Outside L.Q (slot 4 1) (slot 4 10 - slot 4 1) m m' := fun h h1 h2 =>
    h.mono (by simp only [slot_eq]; omega) (by simp only [slot_eq] at h2 ⊢; omega)
  refine ⟨⟨Q14.step kt (by decide), ?_, ?_, ⟨s₁₄.mem, ?_, wo⟩⟩, kall.mono (by decide)⟩
  · show arr t.mem L.Q 4 9 = _
    rw [wq 9 (by decide), m14, ae o13 (by omega) 9 (by decide) (by decide),
      ae o12 (by omega) 9 (by decide) (by decide), A9]
  · rw [mt, word_writeW_self, d22, ae o13 (by omega) 9 (by decide) (by decide),
      ae o12 (by omega) 9 (by decide) (by decide), ae o12 (by omega) 5 (by decide) (by decide),
      ae o12 (by omega) 0 (by decide) (by decide), A9, A6, A5, A0]
    simp only [Bool.and_assoc, Bool.decide_and]
  · rw [m14, m11, m9, m7, m4] at *
    exact (((((((mo o3' (Nat.le_refl _) (by decide)).trans (mo o5 (by decide) (by decide))).trans
      (mo o6 (by decide) (by decide))).trans (mo o8 (by decide) (by decide))).trans
      (mo o10 (by decide) (by decide))).trans (mo o12 (by decide) (by decide))).trans
      (mo o13 (by decide) (by decide)))

end VG.Proof.Dsa.PPC64LE
