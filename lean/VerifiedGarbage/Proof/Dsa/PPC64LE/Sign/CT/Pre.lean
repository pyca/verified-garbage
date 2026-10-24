module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Body
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Keep9
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Inverse
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.S
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# DSA signing on PPC64LE: the body up to the load of `out`

The taint analysis treats memory as secret, so `out`, which `output` loads
from the header's word `hOut`, is secret to it. `spre_ok`: the body up to
that load (`spre`, the body's sequence regrouped there) runs from the state
`checkKey` leaves for it and loads `out` into `r12`, with `q_len` in `r6`, in
the Q space; the constant-time proof fixes those registers there.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Impl.MillerRabin.PPC64LE (sel)
open VG.Proof.Bignum (slot)

/-- `output` up to the load of `out` (and `q_len`). -/
def soutPre : Prog isa :=
  .seq (Verify.zeroArr 7) (.seq (.block [.load .d .r22 .r21 hMask]) (.seq (nonZero 6)
    (.seq (.block [.addi .r20 .r22 0]) (.seq (sel 1 9 7) (.seq (sel 2 6 7)
      (.block ([.load .d .r12 .r21 hOut] ++ getQ .r6)))))))

/-- The body up to the load of `out`. -/
def spre : Prog isa :=
  .seq keyPair (.seq gk (.seq rRanges (.seq Verify.rrQ (.seq Verify.qMinus2 (.seq inverseK
    (.seq sValue soutPre))))))

theorem soutPre_ok {s : State} {L : Lay} {key nonce dig out : Addr} {b : Bool} (hL : L.Ok)
    (h : QS s L key nonce dig) (hw : word s.mem L.S hOut = out) (hm : word s.mem L.S hMask = mask b) :
    WP isa soutPre s fun t =>
      (QS t L key nonce dig ∧ QArr L s.mem t.mem ∧ t.gpr .r12 = out ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql) ∧
        Keep outputRegs s t := by
  have hZ := hL.z256
  unfold soutPre
  -- 0 into array 7.
  refine WP.seq (WP.mono (zeroArr_ok h.inq.env (j := 7) (by decide)) fun s₁ ⟨⟨z7, o1⟩, k1⟩ => ?_)
  have Q1 := h.step k1 (by decide)
  have qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  -- The mask into `r22`.
  have hld : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r21 + BitVec.ofNat 64 hMask) 8 := by
    rw [Q1.regs.r21]; exact Q1.scr.ld (show hMask + 8 ≤ L.Z by simp only [hMask]; omega)
  have hw1 : word s₁.mem L.S hMask = mask b := (Body.hMask (qa1.qbody.body hL)).trans hm
  refine WP.seq (WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = mask b ∧ u.mem = s₁.mem)
    (by prun [exec_ld (by decide) hld]; rw [Q1.regs.r21, ← hw1]) (by decide)) fun s₂ ⟨⟨a22, m2⟩, k2⟩ => ?_)
  have Q2 := Q1.step k2 (by decide)
  -- `r22 &=` the mask of `s ≠ 0`.
  refine WP.seq (WP.mono (nonZero_ok Q2.inq.env (a := 6) (by decide) (by rw [m2]; exact z7) a22)
    fun s₃ ⟨⟨b22, m3⟩, k3⟩ => ?_)
  have Q3 := Q2.step k3 (by decide)
  generalize (b && decide (arr s₂.mem L.Q 4 6 ≠ 0)) = c at b22
  refine WP.seq (WP.mono (WP.keep [.r20] (Q := fun u => u.gpr .r20 = mask c ∧ u.mem = s₃.mem)
    (by prun [b22, BitVec.add_zero]) (by decide)) fun s₄ ⟨⟨a20, m4⟩, k4⟩ => ?_)
  have Q4 := Q3.step k4 (by decide)
  have hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  -- The selections into arrays 1 and 2.
  refine WP.seq (WP.mono (sel_ok Q4.inq.env (b := c) (o := 1) (a := 9) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) a20) fun s₅ ⟨⟨_, o5⟩, k5⟩ => ?_)
  have Q5 := Q4.step k5 (by decide)
  refine WP.seq (WP.mono (sel_ok Q5.inq.env (b := c) (o := 2) (a := 6) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) ((k5.gpr .r20 (by decide)).trans a20)) fun s₆ ⟨⟨_, o6⟩, k6⟩ => ?_)
  have Q6 := Q5.step k6 (by decide)
  have qa6 : QArr L s.mem s₆.mem := by
    refine qa1.trans ?_
    rw [← hm4]
    exact (QArr.of o5 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)).trans
      (QArr.of o6 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega))
  have K6 := ((((k1.trans k2).trans k3).trans k4).trans k5).trans k6
  -- `out` into `r12`, `q_len` into `r6`.
  rw [WP.block_append_iff]
  have hld' : InRegions (s₆.rd ++ s₆.wr) (s₆.gpr .r21 + BitVec.ofNat 64 hOut) 8 := by
    rw [Q6.regs.r21]; exact Q6.scr.ld (show hOut + 8 ≤ L.Z by simp only [hOut]; omega)
  have hwo : word s₆.mem L.S hOut = out := (Body.hOut (qa6.qbody.body hL)).trans hw
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = out ∧ u.mem = s₆.mem)
    (by prun [exec_ld (by decide) hld']; rw [Q6.regs.r21]; exact hwo) (by decide)) fun s₇ ⟨⟨a12, m7⟩, k7⟩ => ?_
  refine WP.mono (getQ_ok (Q6.regs.keep k7) .r6) fun t ⟨⟨a6, m8⟩, k8⟩ => ?_
  have k78 := k7.trans k8
  exact ⟨⟨Q6.step k78 (by decide), by rw [m8, m7]; exact qa6, (k8.gpr .r12 (by decide)).trans a12, a6⟩,
    (K6.trans k78).mono (by decide)⟩

theorem spre_ok {s₀ s : State} {L : Lay} {key nonce dig out : Addr} {d : Nat}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key nonce dig d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hw : word s.mem L.S hOut = out) :
    WP isa spre s fun t =>
      (QS t L key nonce dig ∧ Kept L s.mem t.mem ∧ word t.mem L.S hOut = out ∧ t.gpr .r12 = out ∧
        t.gpr .r6 = BitVec.ofNat 64 L.ql) ∧ Keep bodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hnw := hL.nowrap
  have hw16 := hL.wp_ge
  have hbe := hL.buf_end
  have hw8 := hL.wp_eq
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have hqZ : slot L.wp 28 + 1600 ≤ L.Z := by simp only [Lay.bOff, Lay.qOff] at hbe; omega
  have e8 := Lay.slot_eq L.wp 8; have e28 := Lay.slot_eq L.wp 28
  obtain ⟨ip, scr, regs, p0, -, p8, q0, -, r2⟩ := hc
  have hk3 : Src s L key (3 * L.pl + L.ql) := hk.take (by omega)
  obtain ⟨-, eq, -, -⟩ := key_kept hk3 hkp.out
  unfold KeyOk at hK
  have hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at hK p0 p8
  generalize qOf s₀.mem L key = q at hK q0 r2 hqlt
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  have hq8 : Spec.Dsa.bitLength q = 8 * (Spec.Dsa.bitLength q / 8) := by
    have := hK.1.1; unfold Spec.Dsa.supportedSizes at this; omega
  generalize Spec.Dsa.bitLength q / 8 = n at r2 hq8
  have hnq : n ≤ L.ql := by
    have hq0 : q ≠ 0 := by omega
    have hlog : q.log2 < 8 * L.ql := (Nat.log2_lt hq0).mpr hqlt
    have : Spec.Dsa.bitLength q = q.log2 + 1 := by simp [Spec.Dsa.bitLength, hq0]
    omega
  have hdgn : Src s L dig (min d n) := hdg.take (Nat.min_le_left _ _)
  unfold spre
  -- The mask of `g^x mod p = y`.
  refine WP.seq (WP.mono (keyPair_ok (p := p) hL scr regs ip hk p0 (by omega) hpo p8)
    fun s₁ ⟨⟨mx₁, ip₁, o₁, p0₁, _, sav₁, hout₁⟩, k₁⟩ => ?_)
  have K₁ : Kept L s.mem s₁.mem := ⟨o₁.mono (Nat.zero_le _) (by omega), sav₁⟩
  have q0₁ : arrQ s₁.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 (keepQ_of hL fun x hx => o₁ x (Or.inr (by omega))) (by decide) (by decide)]
    exact q0
  have p8₁ : arrP s₁.mem L 8 = arrP s.mem L 8 :=
    Outside.val32 o₁ (Or.inr (by omega)) (by omega)
  -- `g^k mod p` to the buffer.
  refine WP.seq (WP.mono (gk_ok (p := p) hL (scr.congr k₁.wr) (regs.keep k₁) ip₁ (hk.keep k₁.rd k₁.wr)
      (hn.keep k₁.rd k₁.wr) (p0₁.trans p0) (by omega) hpo (p8₁.trans p8))
    fun s₂ ⟨⟨_, _, B₂, Qk₂, _, _, _⟩, k₂⟩ => ?_)
  have K₂ := K₁.trans (Kept.ofBody hL B₂)
  have k₁₂ := k₁.trans k₂
  have q0₂ : arrQ s₂.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 Qk₂ (by decide) (by decide)]; exact q0₁
  have mx₂ := (Body.hMask B₂).trans mx₁
  have hout₂ : word s₂.mem L.S hOut = out := ((Body.hOut B₂).trans hout₁).trans hw
  -- r, and the masks of the ranges.
  refine WP.seq (WP.mono (rRanges_ok hL (scr.congr k₁₂.wr) ((regs.keep k₁).keep k₂) (hk.keep k₁₂.rd k₁₂.wr)
      (hn.keep k₁₂.rd k₁₂.wr) (by rw [q0₂]; omega) mx₂)
    fun s₃ ⟨⟨Q₃, r9₃, m₃, mf, fa, fb⟩, k₃⟩ => ?_)
  rw [q0₂] at r9₃
  have qa₃ : QArr L s₂.mem mf := QArr.of fa (Nat.le_refl _) (by decide)
  have K₃ := (K₂.trans (Kept.ofBody hL (qa₃.qbody.body hL))).trans (Kept.ofMask hL fb)
  have k₁₃ := k₁₂.trans k₃
  have q0₃ : arrQ s₃.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 (mask_keepQ hL fb) (by decide) (by decide)]; exact qa₃.arr0.trans q0₂
  have hout₃ : word s₃.mem L.S hOut = out := by
    rw [Outside.word fb (Or.inr (by decide)) (by decide), Body.hOut (qa₃.qbody.body hL)]; exact hout₂
  -- `R² mod q`.
  refine WP.seq (WP.mono (rrQ9_ok Q₃ (by rw [q0₃]; omega)) fun s₄ ⟨⟨Q₄, h8₄, qa₄, a9₄⟩, k₄⟩ => ?_)
  rw [q0₃] at h8₄
  have q0₄ : arrQ s₄.mem L 0 = q := qa₄.arr0.trans q0₃
  -- `q − 2`.
  refine WP.seq (WP.mono (qMinus2_9_ok Q₄ hL (by rw [q0₄]; omega) (by rw [q0₄]; exact hqlt))
    fun s₅ ⟨⟨Q₅, _, a8₅, qb₅, a9₅⟩, k₅⟩ => ?_)
  have q0₅ : arrQ s₅.mem L 0 = q := qb₅.arr0.trans q0₄
  have B₃₅ : Body L s₃.mem s₅.mem := (qa₄.qbody.body hL).trans (qb₅.body hL)
  have k₁₅ := (k₁₃.trans k₄).trans k₅
  -- `w = k^(q − 2) mod q`.
  refine WP.seq (WP.mono (inverseK_ok Q₅ hL (hn.keep k₁₅.rd k₁₅.wr) (by rw [q0₅]; omega) (by rw [q0₅]; exact hqo)
      (by rw [a8₅, h8₄, q0₅])) fun s₆ ⟨⟨Q₆, w4₆, a8₆, qa₆, a9₆⟩, k₆⟩ => ?_)
  have q0₆ : arrQ s₆.mem L 0 = q := qa₆.arr0.trans q0₅
  have B₃₆ := B₃₅.trans (qa₆.qbody.body hL)
  have K₆ := K₃.trans (Kept.ofBody hL B₃₆)
  have k₁₆ := k₁₅.trans k₆
  -- s.
  have hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₆.mem dig (min d n)) < 2 * arrQ s₆.mem L 0 := by
    rw [q0₆]
    refine Nat.lt_of_lt_of_le (VG.Proof.Dsa.decodeBE_lt _) ?_
    rw [VG.Proof.Bignum.bytesAt_length]
    refine Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.min_le_right d n)) ?_
    have := pow_bitLength_le (q := q) (by omega)
    rw [hq8, Nat.pow_mul] at this
    exact this
  refine WP.seq (WP.mono (sValue_ok Q₆ hL ((k₁₆.gpr .r2 (by decide)).trans r2) hnq hd
      (hdgn.keep k₁₆.rd k₁₆.wr) (hk.keep k₁₆.rd k₁₆.wr) (by rw [q0₆]; omega) (by rw [q0₆]; exact hqo)
      (by rw [a8₆, a8₅, h8₄, q0₆]) (by rw [w4₆, q0₅, q0₆]; exact Nat.mod_lt _ (by omega))
      (by rw [a9₆, a9₅, a9₄, r9₃, q0₆]; exact Nat.mod_lt _ (by omega)) hz)
    fun s₇ ⟨⟨Q₇, _, _, qa₇⟩, k₇⟩ => ?_)
  have B₃₇ := B₃₆.trans (qa₇.qbody.body hL)
  have K₇ := K₃.trans (Kept.ofBody hL B₃₇)
  have k₁₇ := k₁₆.trans k₇
  -- The output, up to the load of `out`.
  refine WP.mono (soutPre_ok hL Q₇ ((Body.hOut B₃₇).trans hout₃) ((Body.hMask B₃₇).trans m₃))
    fun t ⟨⟨Qt, qat, t12, t6⟩, kt⟩ => ⟨⟨Qt, K₇.trans (Kept.ofBody hL (qat.qbody.body hL)),
      (Body.hOut (qat.qbody.body hL)).trans ((Body.hOut B₃₇).trans hout₃), t12, t6⟩,
      keep_but21 (k₁₇.trans kt) (by decide) (by decide)⟩

end VG.Proof.Dsa.PPC64LE
