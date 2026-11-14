module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Gk
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.KeyPair
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
import VerifiedGarbage.Proof.Dsa.PPC64LE.ReduceQ
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
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

* `nonZero_ok`: `r22 &=` the mask of `[a] ≠ c`, with c in array 7;
* `rRanges_ok`: in the Q space, `R² mod q` (`rrQ_ok`), `r = (g^k mod p) mod q`
  (`vModQ_ok`, from the P space's array 4) into array 9, and the header's word
  `hMask &=` the masks of `0 < k < q`, `0 < x < q` and `r ≠ 0`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot slot_sep)

/-- The registers `nonZero` writes. -/
def nonZeroRegs : List Reg := [.r20] ++ eqRegs .r19 ++ [.r20, .r22]

/-- `nonZero a`: `r22 &=` the mask of `[a] ≠ c`, with c in array 7 (0 for
`[a] ≠ 0`). -/
theorem nonZero_ok {s : State} {B : Addr} {Z w a c : Nat} {b : Bool} (h : Env s B Z w) (ha : a < 28)
    (h7 : arr s.mem B w 7 = c) (h22 : s.gpr .r22 = mask b) :
    WP isa (nonZero a) s fun t =>
      (t.gpr .r22 = mask (b && decide (arr s.mem B w a ≠ c)) ∧ t.mem = s.mem) ∧ Keep nonZeroRegs s t := by
  unfold nonZero
  refine WP.seq (WP.mono (ones_ok s) fun s₁ ⟨⟨a20, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (eqMask_ok (h.keep k1 (by decide)) .r19 (a := a) (b := 7) ha (by decide))
    fun s₂ ⟨⟨a19, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.r20, .r22] (Q := fun t => t.gpr .r22 = mask (b && decide (arr s.mem B w a ≠ c)) ∧
      t.mem = s₂.mem) ?_ (by decide)) fun t ⟨⟨t22, tm⟩, kt⟩ => ⟨⟨t22, by rw [tm, m2, m1]⟩, (k12.trans kt).mono (by decide)⟩
  have b20 : s₂.gpr .r20 = mask true := (k2.gpr .r20 (by decide)).trans a20
  have b22 : s₂.gpr .r22 = mask b := (k12.gpr .r22 (by decide)).trans h22
  rw [m1, ← arr, ← arr, h7] at a19
  unfold clear19
  prun [b20, b22, a19, mask_clear, mask_and]
  simp only [Bool.true_and, decide_not]

/-- The registers `rRanges` writes. -/
def rRangesRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r23,
    .r24, .r25, .r29, .r30, .r31]

/-- `rRanges`: from the P space, with `g^k mod p` in its array 4 and in the
buffer: `R² mod q` into the Q space's arrays 1 and 8, r into its array 9, and
`hMask &=` the masks of `0 < k < q`, `0 < x < q` and `r ≠ 0`. Memory changes
only in `scratch` past its header and in `hMask`; q is kept. -/
theorem rRanges_ok {s : State} {L : Lay} {key nonce dig : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key nonce dig) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hP : InP s L) (hv : arrP s.mem L 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl))
    (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) (hm : word s.mem L.S hMask = mask b) :
    WP isa rRanges s fun t =>
      (QS t L key nonce dig ∧
        arrQ t.mem L 9 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 ∧
        word t.mem L.S hMask = mask (b && decide ((0 < kOf s.mem L nonce ∧ kOf s.mem L nonce < arrQ s.mem L 0) ∧
          (0 < xOf s.mem L key ∧ xOf s.mem L key < arrQ s.mem L 0) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 ≠ 0)) ∧
        arrQ t.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0 ∧ arrQ t.mem L 0 = arrQ s.mem L 0 ∧
        (∃ m, Body L s.mem m ∧ Outside L.S hMask 8 m t.mem)) ∧
        Keep rRangesRegs s t := by
  have hql := hL.ql
  have hpl := hL.pl
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hbe := hL.buf_end
  have hnw : slot 4 28 ≤ 2 ^ 64 := by decide
  unfold rRanges
  -- g^k mod p into the P space's array 6.
  refine WP.seq (WP.mono (copy_ok hP.env (o := 6) (a := 4) (by decide) (by decide) (by decide))
    fun s₁ ⟨⟨v6, o1⟩, k1⟩ => ?_)
  have pb1 : PBody L s.mem s₁.mem := o1.mono (by simp only [Lay.slot_eq]; omega_arith)
    (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)
  have aq1 : ∀ j < 28, arrQ s₁.mem L j = arrQ s.mem L j := fun j hj => pb1.arrQ hL j hj
  -- Into the Q space; `R² mod q`.
  refine WP.seq (WP.mono (enterQ_ok hL (hs.congr k1.wr) (hr.keep k1 (by decide))) fun s₂ ⟨⟨q2, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have Q2 : QS s₂ L key nonce dig := ⟨q2, hs.congr k12.wr, hr.keep k12 (by decide)⟩
  have aq2 : ∀ j < 28, arrQ s₂.mem L j = arrQ s.mem L j := fun j hj => by rw [arrQ, arr, m2]; exact aq1 j hj
  refine WP.seq (WP.mono (rrQ_ok Q2 (by rw [aq2 0 (by decide)]; exact hq2) (by rw [aq2 0 (by decide)]; exact hqo))
    fun s₃ ⟨⟨Q3, h8₃, qa3, _, h1₃⟩, k3⟩ => ?_)
  rw [aq2 0 (by decide)] at h8₃ h1₃
  have k13 := k12.trans k3
  have q0₃ : arrQ s₃.mem L 0 = arrQ s.mem L 0 := qa3.arr0.trans (aq2 0 (by decide))
  -- r = (g^k mod p) mod q into array 4.
  refine WP.seq (WP.mono (vModQ_ok hL Q3.scr Q3.regs (by rw [q0₃]; exact hq2) (by rw [q0₃]; exact hqo)
      (by rw [h1₃, q0₃])) fun s₄ ⟨⟨q4, r4, a4, a0₄, a1₄, o4⟩, k4⟩ => ?_)
  have p6 : arrP s₃.mem L 6 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) := by
    rw [qa3.qbuf.arrP hL (by decide), arrP, arr, m2]; exact v6.trans hv
  rw [p6, q0₃] at a4
  rw [q0₃] at a0₄
  have B14 : Body L s.mem s₄.mem :=
    ((pb1.body hL).trans (by rw [← m2]; exact qa3.qbody.body hL)).trans
      (o4.mono (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)
        (by simp only [Lay.bOff, Lay.qOff] at hbe ⊢; have : slot 4 24 = 1408 := rfl; omega_arith))
  have k14 : Keep rRangesRegs s s₄ := (k13.trans k4).mono (by decide)
  have Q4 : QS s₄ L key nonce dig := ⟨q4, hs.congr k14.wr, r4⟩
  -- r into array 9, `R² mod q` into array 8, 0 into array 7.
  refine WP.seq (WP.mono (copy_ok Q4.inq.env (o := 9) (a := 4) (by decide) (by decide) (by decide))
    fun s₅ ⟨⟨v9, o5⟩, k5⟩ => ?_)
  have Q5 := Q4.step k5 (by decide)
  refine WP.seq (WP.mono (copy_ok Q5.inq.env (o := 8) (a := 1) (by decide) (by decide) (by decide))
    fun s₅' ⟨⟨v8, o5'⟩, k5'⟩ => ?_)
  have Q5' := Q5.step k5' (by decide)
  refine WP.seq (WP.mono (zeroArr_ok Q5'.inq.env (j := 7) (by decide)) fun s₆ ⟨⟨z7, o6⟩, k6⟩ => ?_)
  have Q6 := Q5'.step k6 (by decide)
  have k16 : Keep rRangesRegs s s₆ := (((k14.trans k5).trans k5').trans k6).mono (by decide)
  -- k into array 6, x into array 5.
  refine WP.seq (WP.mono (ptrR_ok Q6.regs) fun s₇ ⟨⟨b12, b6, m7⟩, k7⟩ => ?_)
  have Q7 := Q6.step k7 (by decide)
  have k17 := k16.trans k7
  refine WP.seq (WP.mono (loadQ_ok (j := 6) Q7 hL (by decide) (by decide) (hn.keep k17.rd k17.wr) b12 b6
      (by omega_arith) (by omega_arith)) fun s₈ ⟨⟨Q8, v6', top6, o8, qa8⟩, k8⟩ => ?_)
  refine WP.seq (WP.mono (ptrX_ok Q8.regs) fun s₉ ⟨⟨c12, c6, m9⟩, k9⟩ => ?_)
  have Q9 := Q8.step k9 (by decide)
  have k19 : Keep rRangesRegs s s₉ := ((k17.trans k8).trans k9).mono (by decide)
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q9 hL (by decide) (by decide)
      ((hk.keep k19.rd k19.wr).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)) c12 c6
      (by omega_arith) (by omega_arith)) fun s₁₀ ⟨⟨Q10, v5, top5, o10, qa10⟩, k10⟩ => ?_)
  have k110 : Keep rRangesRegs s s₁₀ := (k19.trans k10).mono (by decide)
  have ae : ∀ {m m' : Mem} {o n : Nat}, Outside L.Q (slot 4 o) n m m' → n ≤ 48 → ∀ j, j < 28 → j ≠ o →
      arr m' L.Q 4 j = arr m L.Q 4 j := fun h hn' j hj ho =>
    Outside.arrEq (h.mono (Nat.le_refl _) (by omega_arith)) hj ho hnw
  have qa47 : QArr L s₄.mem s₇.mem := by
    rw [m7]
    exact ((QArr.of o5 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)).trans
      (QArr.of o5' (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))).trans
      (QArr.of o6 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))
  have qa49 : QArr L s₄.mem s₉.mem := by rw [m9]; exact qa47.trans qa8
  have qa410 : QArr L s₄.mem s₁₀.mem := qa49.trans qa10
  have B17 : Body L s.mem s₇.mem := B14.trans (qa47.qbody.body hL)
  have B19 : Body L s.mem s₉.mem := B14.trans (qa49.qbody.body hL)
  have B110 : Body L s.mem s₁₀.mem := B14.trans (qa410.qbody.body hL)
  -- `hMask` into `r22`.
  have h21 : s₁₀.gpr .r21 = L.S := Q10.regs.r21
  have hld : InRegions (s₁₀.rd ++ s₁₀.wr) (s₁₀.gpr .r21 + BitVec.ofNat 64 hMask) 8 := by
    rw [h21]; exact Q10.scr.ld (show hMask + 8 ≤ L.Z by simp only [hMask]; omega_arith)
  have hw10 : word s₁₀.mem L.S hMask = mask b := by
    rw [Outside.word B110 (Or.inl (by simp only [hMask]; omega_arith)) (by simp only [hMask]; omega_arith)]
    exact hm
  refine WP.seq (WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = mask b ∧ u.mem = s₁₀.mem)
    (by prun [exec_ld (by decide) hld]; rw [h21, ← hw10]) (by decide)) fun s₁₁ ⟨⟨a22, m11⟩, k11⟩ => ?_)
  have Q11 := Q10.step k11 (by decide)
  -- The values in arrays 0, 5, 6, 8 and 9.
  have A0 : arr s₁₁.mem L.Q 4 0 = arrQ s.mem L 0 := by rw [m11]; exact qa410.arr0.trans a0₄
  have A6 : arr s₁₁.mem L.Q 4 6 = kOf s.mem L nonce := by
    rw [m11, ae o10 (by omega_arith) 6 (by decide) (by decide), m9]
    refine v6'.trans ?_
    rw [kOf, hn.bytes B17 hZ]
  have A5 : arr s₁₁.mem L.Q 4 5 = xOf s.mem L key := by
    rw [m11]
    refine v5.trans ?_
    rw [xOf, (hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)).bytes B19 hZ]
  have A9 : arr s₁₁.mem L.Q 4 9 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 := by
    rw [m11, ae o10 (by omega_arith) 9 (by decide) (by decide), m9, ae o8 (by omega_arith) 9 (by decide) (by decide), m7,
      ae o6 (by omega_arith) 9 (by decide) (by decide), ae o5' (by omega_arith) 9 (by decide) (by decide), v9]
    exact a4
  have A8 : arr s₁₁.mem L.Q 4 8 = 2 ^ (128 * 4) % arrQ s.mem L 0 := by
    rw [m11, ae o10 (by omega_arith) 8 (by decide) (by decide), m9, ae o8 (by omega_arith) 8 (by decide) (by decide), m7,
      ae o6 (by omega_arith) 8 (by decide) (by decide), v8, ae o5 (by omega_arith) 1 (by decide) (by decide)]
    exact a1₄.trans h1₃
  have z7' : arr s₁₁.mem L.Q 4 7 = 0 := by
    rw [m11, ae o10 (by omega_arith) 7 (by decide) (by decide), m9, ae o8 (by omega_arith) 7 (by decide) (by decide), m7]
    exact z7
  have top6' : word s₁₁.mem L.Q (slot 4 6 + 8 * 4) = 0 := by
    rw [m11, Outside.word o10 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith), m9]; exact top6
  -- The ranges and `r ≠ 0`.
  refine WP.seq (WP.mono (inRange_ok Q11.inq.env (a := 6) (b := b) (by decide) (by decide) top6' z7' a22)
    fun s₁₂ ⟨⟨b22, o12⟩, k12'⟩ => ?_)
  have Q12 := Q11.step k12' (by decide)
  have top5' : word s₁₂.mem L.Q (slot 4 5 + 8 * 4) = 0 := by
    rw [Outside.word o12 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith), m11]; exact top5
  refine WP.seq (WP.mono (inRange_ok Q12.inq.env (a := 5) (b := _) (by decide) (by decide) top5'
    (by rw [ae o12 (by omega_arith) 7 (by decide) (by decide)]; exact z7') b22) fun s₁₃ ⟨⟨c22, o13⟩, k13'⟩ => ?_)
  have Q13 := Q12.step k13' (by decide)
  refine WP.seq (WP.mono (nonZero_ok Q13.inq.env (a := 9) (c := 0) (by decide)
    (by rw [ae o13 (by omega_arith) 7 (by decide) (by decide), ae o12 (by omega_arith) 7 (by decide) (by decide)]; exact z7')
    c22) fun s₁₄ ⟨⟨d22, m14⟩, k14'⟩ => ?_)
  have Q14 := Q13.step k14' (by decide)
  -- The mask to `hMask`.
  have h21' : s₁₄.gpr .r21 = L.S := Q14.regs.r21
  have hst : InRegions s₁₄.wr (L.S + BitVec.ofNat 64 hMask) 8 := Q14.scr.st (by simp only [hMask]; omega_arith)
  have he : exec (.store .d .r22 .r21 hMask) s₁₄ =
      some { s₁₄ with mem := s₁₄.mem.writeW (L.S + BitVec.ofNat 64 hMask) (s₁₄.gpr .r22) } := by
    rw [exec_std (by decide) (by rw [h21']; exact hst), h21']
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s₁₄.mem.writeW (L.S + BitVec.ofNat 64 hMask) (s₁₄.gpr .r22))
    (by prun [he]) (by decide)) fun t ⟨mt, kt⟩ => ?_
  have wo : Outside L.S hMask 8 s₁₄.mem t.mem := by
    rw [mt]; exact writeW_outside s₁₄.mem L.S (d := hMask) _ (by simp only [hMask]; omega_arith)
  have wq : ∀ j, j < 28 → arr t.mem L.Q 4 j = arr s₁₄.mem L.Q 4 j := fun j hj =>
    Outside.val32 (mask_keepQ hL wo) (Or.inl (by simp only [slot_eq]; omega_arith)) (by simp only [slot_eq]; omega_arith)
  have kall := ((((k110.trans k11).trans k12').trans k13').trans k14').trans kt
  have q1213 : ∀ j, j < 28 → j ≠ 3 → arr s₁₄.mem L.Q 4 j = arr s₁₁.mem L.Q 4 j := fun j hj h3 => by
    rw [m14, ae o13 (by omega_arith) j hj h3, ae o12 (by omega_arith) j hj h3]
  have B114 : Body L s.mem s₁₄.mem := by
    rw [m14]
    exact ((show Body L s.mem s₁₁.mem by rw [m11]; exact B110).trans
      (Body.ofQ hL o12 (by decide))).trans
      (Body.ofQ hL o13 (by decide))
  refine ⟨⟨Q14.step kt (by decide), ?_, ?_, ?_, ?_, ⟨s₁₄.mem, B114, wo⟩⟩, kall.mono (by decide)⟩
  · show arr t.mem L.Q 4 9 = _
    rw [wq 9 (by decide), q1213 9 (by decide) (by decide), A9]
  · rw [mt, word_writeW_self, d22, ae o13 (by omega_arith) 9 (by decide) (by decide),
      ae o12 (by omega_arith) 9 (by decide) (by decide), ae o12 (by omega_arith) 5 (by decide) (by decide),
      ae o12 (by omega_arith) 0 (by decide) (by decide), A9, A6, A5, A0]
    simp only [Bool.and_assoc, Bool.decide_and]
  · show arr t.mem L.Q 4 8 = _
    rw [wq 8 (by decide), q1213 8 (by decide) (by decide), A8]
  · show arr t.mem L.Q 4 0 = _
    rw [wq 0 (by decide), q1213 0 (by decide) (by decide), A0]

end VG.Proof.Dsa.PPC64LE
