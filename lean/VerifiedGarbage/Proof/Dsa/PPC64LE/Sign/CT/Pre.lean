module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Body
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
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
  refine WP.seq (WP.mono (nonZero_ok Q2.inq.env (a := 6) (c := 0) (by decide) (by rw [m2]; exact z7) a22)
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
  unfold spre
  exact sprefix_ok hL hK hc hkp hk hn hd hdg hw fun t Qt Kt ht hm _ _ kt =>
    WP.mono (soutPre_ok hL Qt ht hm) fun u ⟨⟨Qu, qau, u12, u6⟩, ku⟩ =>
      ⟨⟨Qu, Kt.trans (Kept.ofBody hL (qau.qbody.body hL)), (Body.hOut (qau.qbody.body hL)).trans ht, u12, u6⟩,
        keep_but21 (kt.trans ku) (by decide) (by decide)⟩

end VG.Proof.Dsa.PPC64LE
