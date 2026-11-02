module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignKeyPair
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on RISC-V: r and the ranges

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/R.lean`). `rRanges_ok`: in the Q
space, `r = (g^k mod p) mod q` (`reduce64` of the buffer's `p_len` octets)
into array 25, and the header's word `hMask &=` the masks of `0 < k < q`,
`0 < x < q` and `r ≠ 0`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- An array of the Q space, kept by a change apart from it. -/
theorem qa_eq {L : Lay} (hL : L.Ok) {m m' : Mem} {o n j : Nat} (h : Outside L.Q o n m m') (hj : j < 28)
    (hd : slot L.wq j + 8 * L.wq ≤ o ∨ o + n ≤ slot L.wq j) : arrQ m' L j = arrQ m L j := by
  have := slot_lt (w := L.wq) hj
  have := hL.wq_ge
  exact h.wordsVal hd (by simp only [Lay.slot_eq] at *; omega)

/-- The registers `rRanges` writes. -/
def rRangesRegs : List Reg :=
  enterRegs ++ [.s9, .t2] ++ [.s10] ++ (VG.Proof.Bignum.RISCV64.redRegs ++ [.a2, .a5, .a6]) ++ copyRegs ++
    [.s0, .t3, .t5] ++ [.s7, .s8] ++ loadRegs ++ ptrRegs ++ loadRegs ++ [.a4] ++ inRangeRegs ++ inRangeRegs ++
    nonZeroRegs

/-- `rRanges`: in the Q space, r into array 25, and `hMask &=` the masks of
`0 < k < q`, `0 < x < q` and `r ≠ 0`. Memory changes only in the Q space's
arrays 1–27 and in `hMask`. -/
theorem rRanges_ok {s : State} {L : Lay} {key nonce : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key nonce) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hq : 0 < arrQ s.mem L 0) (hm : word s.mem L.S hMask = mask b) :
    WP isa rRanges s fun t =>
      (QS t L key nonce ∧
        arrQ t.mem L 25 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 ∧
        word t.mem L.S hMask = mask (b && decide ((0 < kOf s.mem L nonce ∧ kOf s.mem L nonce < arrQ s.mem L 0) ∧
          (0 < xOf s.mem L key ∧ xOf s.mem L key < arrQ s.mem L 0) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 ≠ 0)) ∧
        (∃ m, QArr L s.mem m ∧ Outside L.S hMask 8 m t.mem)) ∧ Keep rRangesRegs s t := by
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  have hZ := hL.z256
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  have e7 := e 7; have e8 := e 8; have e25 := e 25; have e26 := e 26; have e28 := e 28
  unfold rRanges
  -- r into array 1.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  refine WP.mono (bufBase_ok (hs.congr k1.2.2) hL (hr.keepM k1 m1) (rd := .s9) (t := .t2) (by decide) (by decide)
    (by decide)) fun s₁' ⟨⟨a9, m1'⟩, k1'⟩ => ?_
  refine WP.mono (getP_ok (hs.congr (k1.trans k1').2.2) hL ((hr.keepM k1 m1).keepM k1' m1') .s10)
    fun s₂ ⟨⟨a10, m2⟩, k2'⟩ => ?_
  have k2 := k1'.trans k2'
  replace a9 : s₂.gpr .s9 = L.Buf := (k2'.gpr (by decide)).trans a9
  have m21 : s₂.mem = s.mem := by rw [m2, m1', m1]
  have k12 := k1.trans k2
  have e2 := q1.env.keep k2
  refine WP.seq (WP.mono (ModArith.reduce64_ok (B := L.Q) (Z := 1600) (w := L.wq) (D := L.Buf) (L := L.pl)
    e2.hs (by omega) (by omega) (by omega) e2.a7 e2.s5 e2.t0
    (by rw [m21]; exact hq) (by rw [a9]; exact (BitVec.add_zero _).symm) a10 (by omega) (by omega)
    (by have := bufRd hL (hs.congr k12.2.2) (o := 0) (k := L.pl) (by omega)
        simpa only [off, BitVec.add_zero] using this)
    (buf_apartQ L (n := L.pl) (by omega))) fun s₃ ⟨⟨v1, o3⟩, k3⟩ => ?_)
  rw [m21] at v1 o3
  have k13 := k12.trans k3
  have Q3 : QS s₃ L key nonce := ⟨q1.keep (k2.trans k3), hs.congr k13.2.2,
    hr.keep k13 (Body.ofQ hL o3 (by omega))⟩
  -- r into array 25, 0 into array 7.
  refine WP.seq (WP.mono (copy_ok Q3.inq.env (o := 25) (a := 1) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨v25, o4⟩, k4⟩ => ?_)
  have Q4 := Q3.step k4 (Body.ofQ hL o4 (by omega))
  refine WP.seq (WP.mono (zeroArr_ok Q4.inq.env (j := 7) (by decide)) fun s₅ ⟨⟨z7, o5⟩, k5⟩ => ?_)
  have Q5 := Q4.step k5 (Body.ofQ hL o5 (by omega))
  -- k into array 6, x into array 5.
  refine WP.seq (WP.mono (ptrR_ok Q5.scr hL Q5.regs) fun s₆ ⟨⟨b7, b8, m6⟩, k6⟩ => ?_)
  have Q6 := Q5.stepM k6 m6
  have k16 := ((k13.trans k4).trans k5).trans k6
  refine WP.seq (WP.mono (loadQ_ok (j := 6) Q6 hL (by decide) (hn.keep k16.2.1 k16.2.2) b7 b8
      (by omega) (by omega)) fun s₇ ⟨⟨Q7, v6, top6, o7⟩, k7⟩ => ?_)
  refine WP.seq (WP.mono (ptrX_ok Q7.scr hL Q7.regs) fun s₈ ⟨⟨c7, c8, m8⟩, k8⟩ => ?_)
  have Q8 := Q7.stepM k8 m8
  have k18 := (k16.trans k7).trans k8
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q8 hL (by decide)
      ((hk.keep k18.2.1 k18.2.2).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)) c7 c8
      (by omega) (by omega)) fun s₉ ⟨⟨Q9, v5, top5, o9⟩, k9⟩ => ?_)
  have k19 := k18.trans k9
  have qa : QArr L s.mem s₉.mem := by
    have q3 : QArr L s.mem s₃.mem := QArr.of o3 (by omega) (by omega)
    have q4 : QArr L s₃.mem s₄.mem := QArr.of o4 (by omega) (by omega)
    have q5 : QArr L s₄.mem s₅.mem := QArr.of o5 (by omega) (by omega)
    have q7 : QArr L s₆.mem s₇.mem := QArr.of o7 (by omega) (by omega)
    have q9 : QArr L s₈.mem s₉.mem := QArr.of o9 (by omega) (by omega)
    rw [m6] at q7; rw [m8] at q9
    exact (((q3.trans q4).trans q5).trans q7).trans q9
  -- `hMask` into `a4`.
  obtain ⟨hld, hal⟩ := ScrL.hdr Q9.scr hL (d := 0) (by decide) (by decide)
  have hw9 : word s₉.mem L.S hMask = mask b := by
    rw [(qa.body hL).word (by decide)]; exact hm
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask b ∧ u.mem = s₉.mem)
    (by brun [hMask, Q9.regs.s6, hld, hal]; exact hw9) (by decide) (by rfl)) fun s₁₀ ⟨⟨a4, m10⟩, k10⟩ => ?_)
  have Q10 := Q9.stepM k10 m10
  -- The values in arrays 0, 5, 6, 7 and 25.
  have A0 : arrQ s₁₀.mem L 0 = arrQ s.mem L 0 := by rw [m10]; exact qa.arr0 hL
  have b3 : Body L s.mem s₃.mem := Body.ofQ hL o3 (by omega)
  have b5 : Body L s.mem s₅.mem := (b3.trans (Body.ofQ hL o4 (by omega))).trans (Body.ofQ hL o5 (by omega))
  have b7 : Body L s.mem s₇.mem := b5.trans (by rw [← m6]; exact Body.ofQ hL o7 (by omega))
  have A6 : arrQ s₁₀.mem L 6 = kOf s.mem L nonce := by
    rw [m10, qa_eq hL o9 (by decide) (by omega), m8]
    refine v6.trans ?_
    rw [kOf, m6, hn.bytes b5 (by omega)]
  have A5 : arrQ s₁₀.mem L 5 = xOf s.mem L key := by
    rw [m10]
    refine v5.trans ?_
    rw [xOf, m8, (hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)).bytes b7 (by omega)]
  have A25 : arrQ s₁₀.mem L 25 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 := by
    rw [m10, qa_eq hL o9 (by decide) (by omega), m8, qa_eq hL o7 (by decide) (by omega), m6,
      qa_eq hL o5 (by decide) (by omega)]
    rw [arrQ, wordsVal_congr (m := s₃.mem) (d := slot L.wq 1) fun i hi => v25 i (by omega)]
    exact v1
  have z7' : arrQ s₁₀.mem L 7 = 0 := by
    rw [m10, qa_eq hL o9 (by decide) (by omega), m8, qa_eq hL o7 (by decide) (by omega), m6]
    exact z7
  have top6' : word s₁₀.mem L.Q (slot L.wq 6 + 8 * L.wq) = 0 := by
    rw [m10, o9.word (by omega) (by omega), m8]; exact top6
  have top5' : word s₁₀.mem L.Q (slot L.wq 5 + 8 * L.wq) = 0 := by rw [m10]; exact top5
  -- The ranges and `r ≠ 0`.
  refine WP.seq (WP.mono (inRange_ok Q10.inq.env (a := 6) (b := b) (by decide) (by decide) (by decide) top6'
    z7' a4) fun s₁₁ ⟨⟨b4, o11⟩, k11⟩ => ?_)
  have Q11 := Q10.step k11 (Body.ofQ hL o11 (by omega))
  refine WP.seq (WP.mono (inRange_ok Q11.inq.env (a := 5) (b := _) (by decide) (by decide) (by decide)
    (by rw [o11.word (by omega) (by omega)]; exact top5')
    (by rw [show wordsVal s₁₁.mem L.Q (slot L.wq 7) L.wq = arrQ s₁₁.mem L 7 from rfl,
      qa_eq hL o11 (by decide) (by omega)]; exact z7') b4) fun s₁₂ ⟨⟨c4, o12⟩, k12'⟩ => ?_)
  have Q12 := Q11.step k12' (Body.ofQ hL o12 (by omega))
  refine WP.seq (WP.mono (nonZero_ok Q12.inq.env (a := 25) (c := 0) (by decide)
    (by rw [show wordsVal s₁₂.mem L.Q (slot L.wq 7) L.wq = arrQ s₁₂.mem L 7 from rfl,
      qa_eq hL o12 (by decide) (by omega), qa_eq hL o11 (by decide) (by omega)]; exact z7')
    c4) fun s₁₃ ⟨⟨d4, m13⟩, k13'⟩ => ?_)
  have Q13 := Q12.stepM k13' m13
  -- The mask to `hMask`.
  obtain ⟨_, hal'⟩ := ScrL.hdr Q13.scr hL (d := 0) (by decide) (by decide)
  have hst : InRegions s₁₃.wr (off L.S 0) 8 := Q13.scr.st (by omega)
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s₁₃.mem.writeW (off L.S 0) (s₁₃.gpr .a4))
    (by brun [hMask, Q13.regs.s6, hst, hal']) (by decide) (by rfl)) fun t ⟨mt, kt⟩ => ?_
  have wo : Outside L.S hMask 8 s₁₃.mem t.mem := by
    rw [mt]; exact writeW_outside s₁₃.mem L.S _ (by simp only [hMask]; omega)
  have kall := (((((k19.trans k10).trans k11).trans k12').trans k13').trans kt)
  have qa13 : QArr L s.mem s₁₃.mem := by
    rw [m13]
    exact (qa.trans (by rw [← m10]; exact QArr.of o11 (by omega) (by omega))).trans (QArr.of o12 (by omega) (by omega))
  refine ⟨⟨⟨Q13.inq.keep kt, Q13.scr.congr kt.2.2, Q13.regs.keepHdr kt
      (wo.word (Or.inr (by decide)) (by simp only [hLens]; omega))⟩, ?_, ?_, ⟨s₁₃.mem, qa13, wo⟩⟩, ?_⟩
  · rw [qa_eq hL (mask_keepQ hL wo) (by decide) (Or.inl (by omega)), m13, qa_eq hL o12 (by decide) (by omega),
      qa_eq hL o11 (by decide) (by omega), A25]
  · rw [mt, show off L.S 0 = off L.S hMask from rfl, word_writeW_self, d4, show wordsVal s₁₂.mem L.Q (slot L.wq 25) L.wq = arrQ s₁₂.mem L 25 from rfl,
      qa_eq hL o12 (by decide) (by omega), qa_eq hL o11 (by decide) (by omega),
      show wordsVal s₁₁.mem L.Q (slot L.wq 5) L.wq = arrQ s₁₁.mem L 5 from rfl,
      show wordsVal s₁₁.mem L.Q (slot L.wq 0) L.wq = arrQ s₁₁.mem L 0 from rfl,
      qa_eq hL o11 (by decide) (by omega), qa_eq hL o11 (by decide) (by omega),
      show wordsVal s₁₀.mem L.Q (slot L.wq 6) L.wq = arrQ s₁₀.mem L 6 from rfl,
      show wordsVal s₁₀.mem L.Q (slot L.wq 0) L.wq = arrQ s₁₀.mem L 0 from rfl, A25, A6, A5, A0]
    simp only [Bool.and_assoc, Bool.decide_and]
  · simp only [rRangesRegs, List.append_assoc] at kall ⊢
    exact kall.mono (by decide)

end VG.Proof.Dsa.RISCV64
