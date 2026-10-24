module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Comb.Pow
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Gk
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.R
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Pow
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyComb
import VerifiedGarbage.Proof.Dsa.PPC64LE.Range
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA key derivation on PPC64LE: y

`yValue_ok`: in the P space with p in array 0 and `R² mod p` in array 8,
`y = g^x mod p` (x the `q_len` octets at `r28`) to the buffer's first
`p_len` octets, and `r22 :=` the mask of `y ≠ 0` and `y ≠ 1`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The registers `yValue` writes. -/
def yValueRegs : List Reg :=
  [.r24, .r0, .r6, .r12] ++ combPowRegs ++ [.r14, .r17, .r22] ++ nonZeroRegs ++ storeRegs

/-- `yValue`: `y = g^x mod p` to the buffer's first `p_len` octets, and
`r22 :=` the mask of `y ≠ 0` and `y ≠ 1`. Memory changes only in the P
space's arrays and the buffer's first `p_len` octets. -/
theorem yValue_ok {s : State} {L : Lay} {key x out : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key x out) (hin : InP s L) (hk : Src s L key (2 * L.pl + L.ql)) (hx : Src s L x L.ql)
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 8 = 2 ^ (128 * L.wp) % p) :
    WP isa yValue s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) = gOf s.mem L key ^ kOf s.mem L x % p ∧
        t.gpr .r22 = mask (decide (gOf s.mem L key ^ kOf s.mem L x % p ≠ 0) &&
          decide (gOf s.mem L key ^ kOf s.mem L x % p ≠ 1)) ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem) ∧
        Keep yValueRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hql := hL.ql
  have hpl := hL.pl
  have hbe := hL.buf_end
  have hqZ : L.qOff + 1600 ≤ L.Z := by simp only [Lay.bOff] at hbe; omega
  have e0 := Lay.slot_eq L.wp 0; have e1 := Lay.slot_eq L.wp 1; have e4 := Lay.slot_eq L.wp 4
  have e7 := Lay.slot_eq L.wp 7; have e8 := Lay.slot_eq L.wp 8; have e28 := Lay.slot_eq L.wp 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold yValue
  -- The pointers: x into `r24`, g's octets into `r12`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r24] (Q := fun u => u.gpr .r24 = x ∧ u.mem = s.mem)
    (by prun [hr.r28, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a24, m1⟩, k1⟩ => ?_
  refine WP.mono (ptrG_ok (hr.keep k1)) fun s₂ ⟨⟨b12, _, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  -- `g^x mod p` into array 4.
  refine WP.seq (WP.mono (powSrc_ok (N := off key (L.pl + L.ql)) (E := x) (p := p) hL
      (hr.keep k12) (hin.keep k12 (by decide))
      ((hk.keep k12.rd k12.wr).sub (o := L.pl + L.ql) (k := L.pl) (by omega)) b12 (hx.keep k12.rd k12.wr)
      ((k2.gpr .r24 (by decide)).trans a24) (by rw [hm2]; exact hp0) hp hpo (by rw [hm2]; exact hrr))
    fun s₃ ⟨⟨v4, in3, o3⟩, k3⟩ => ?_)
  rw [hm2] at v4 o3
  have k13 := k12.trans k3
  have y4 : arr s₃.mem L.S L.wp 4 = gOf s.mem L key ^ kOf s.mem L x % p := v4
  have hyp : gOf s.mem L key ^ kOf s.mem L x % p < p := Nat.mod_lt _ (by omega)
  generalize gOf s.mem L key ^ kOf s.mem L x % p = y at y4 hyp ⊢
  -- 0 into array 7, `r22 :=` all ones.
  refine WP.seq (WP.mono (zeroArr_ok in3.env (j := 7) (by decide)) fun s₄ ⟨⟨z7, o4⟩, k4⟩ => ?_)
  have en4 := in3.env.keep k4 (by decide)
  refine WP.seq (WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = mask true ∧ u.mem = s₄.mem)
    (by prun []; rfl) (by decide)) fun s₅ ⟨⟨a22, m5⟩, k5⟩ => ?_)
  have en5 := en4.keep k5 (by decide)
  have y5 : arr s₅.mem L.S L.wp 4 = y := by
    rw [m5, arr, Outside.val32 o4 (by omega) (by omega)]; exact y4
  -- `r22 &=` the masks of `y ≠ 0` and `y ≠ 1`.
  refine WP.seq (WP.mono (nonZero_ok en5 (a := 4) (c := 0) (by decide) (by rw [m5]; exact z7) a22)
    fun s₆ ⟨⟨b22, m6⟩, k6⟩ => ?_)
  rw [y5] at b22
  have en6 := en5.keep k6 (by decide)
  refine WP.seq (WP.mono (Pub.oneP_ok en6.hs (by omega) (by omega) (by omega) en6.h10 en6.h29 en6.h11)
    fun s₇ ⟨⟨v7, o7⟩, k7⟩ => ?_)
  have en7 := en6.keep k7 (by decide)
  have y7 : arr s₇.mem L.S L.wp 4 = y := by
    rw [arr, Outside.val32 o7 (by omega) (by omega), m6]; exact y5
  refine WP.seq (WP.mono (nonZero_ok en7 (a := 4) (c := 1) (by decide) v7
    ((k7.gpr .r22 (by decide)).trans b22)) fun s₈ ⟨⟨c22, m8⟩, k8⟩ => ?_)
  rw [y7, Bool.true_and] at c22
  have en8 := en7.keep k8 (by decide)
  -- y to the buffer.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have k18 := (((((k13.trans k4).trans k5).trans k6).trans k7).trans k8)
  refine WP.mono (bufBase_ok hL (hr.keep k18) (rd := .r12) (t := .r0) (by decide)) fun s₉ ⟨⟨c12, m9⟩, k9⟩ => ?_
  refine WP.mono (getP_ok ((hr.keep k18).keep k9) .r6) fun s₁₀ ⟨⟨c6, m10⟩, k10⟩ => ?_
  have k910 := k9.trans k10
  have hm10 : s₁₀.mem = s₇.mem := by rw [m10, m9, m8]
  refine WP.mono (storeBE_ok (j := 4) (O := L.Buf) (k := L.pl) (en8.keep k910 (by decide)) (by decide)
    (ScrL.bufN (hs.congr (k18.trans k910).wr) hL (by omega)) ((k10.gpr .r12 (by decide)).trans c12) c6
    (by omega) (by omega) (combBufPastP hL)) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [hm10] at vt ot
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← hp0, ← hw8, show 8 * (8 * L.wp) = 32 * (2 * L.wp) by omega]; exact val32_lt _ _ _ _
  have y7' : val32 s₇.mem L.S (slot L.wp 4) (2 * L.wp) = y := y7
  have hm6 : s₆.mem = s₄.mem := by rw [m6, m5]
  have o47 : Outside L.S (slot L.wp 7) (8 * L.wp) s₃.mem s₇.mem := by
    rw [← hm6] at o4; exact o4.trans o7
  have kall := (k18.trans k910).trans kt
  refine ⟨⟨?_, (kt.gpr .r22 (by decide)).trans ((k910.gpr .r22 (by decide)).trans c22),
    ⟨en8.keep (k910.trans kt) (by decide), (kall.gpr .r21 (by decide)).trans hin.h21,
      (kall.gpr .r23 (by decide)).trans hin.h23⟩,
    ((Body.ofP hL o3 (by omega) (by omega)).trans (Body.ofP hL o47 (by omega) (by omega))).trans
      (Body.ofBuf hL ot (by omega)),
    ((comb_pbody_keepQ hL (o3.mono (by omega) (by omega))).trans
      (comb_pbody_keepQ hL (o47.mono (by omega) (by omega)))).trans (combBufKeepQ ot (by omega))⟩,
    kall.mono (by decide)⟩
  rw [vt, read_low (w := L.wp) _ _ (by omega) (by rw [y7']; exact Nat.lt_trans hyp hplt), y7']

end VG.Proof.Dsa.PPC64LE
