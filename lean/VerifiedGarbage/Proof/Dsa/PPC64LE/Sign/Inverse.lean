module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Gk
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr

/-!
# DSA signing on PPC64LE: `w = k^(q − 2) mod q`

`inverseK_ok`: verification's `inverse_ok` (`VerifyInv.lean`) with the base
k, the nonce at `r28`, in place of s.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
  VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot slot_sep)

theorem inverseK_ok {s : State} {L : Lay} {key sig dig : Addr} (h : QS s L key sig dig) (hL : L.Ok)
    (hsg : Src s L sig L.ql) (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h8 : arrQ s.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0) :
    WP isa inverseK s fun t =>
      (QS t L key sig dig ∧
        arrQ t.mem L 4 = kOf s.mem L sig ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) %
          arrQ s.mem L 0 ∧
        arrQ t.mem L 8 = arrQ s.mem L 8 ∧ QArr L s.mem t.mem ∧ arrQ t.mem L 9 = arrQ s.mem L 9) ∧
        Keep invRegs s t := by
  have hRR := pow_sq_eq 4
  generalize (2 : Nat) ^ (128 * 4) = R2 at h8 hRR
  have hql := hL.ql
  have hpl := hL.pl
  have e70 : slot 4 0 = 256 := rfl
  have e71 : slot 4 1 = 304 := rfl
  have e74 : slot 4 4 = 448 := rfl
  have e78 : slot 4 8 = 640 := rfl
  unfold inverseK
  refine WP.seq (WP.mono (ptrR_ok h.regs) fun s₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have Q1 := h.step k1 (by decide)
  refine WP.seq (WP.mono (loadQ_ok (j := 4) Q1 hL (by decide) (by decide)
      ((hsg.keep k1.rd k1.wr).sub (o := 0) (k := L.ql) (by omega)) (by rw [a12, off, BitVec.add_zero]) a6
      (by omega) (by omega))
    fun s₂ ⟨⟨Q2, v4, _, o2, qa2⟩, k2⟩ => ?_)
  rw [m1, off, BitVec.add_zero] at v4
  rw [m1] at o2 qa2
  refine WP.seq (WP.mono (copy_ok Q2.inq.env (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨v1, o3⟩, k3⟩ => ?_)
  have qa3 : QArr L s₂.mem s₃.mem := QArr.of o3 (by rw [e71]) (by rw [e71]; decide)
  have Q3 := Q2.step k3 (by decide)
  have a8s : arr s₂.mem L.Q 4 8 = arrQ s.mem L 8 := Outside.val32 o2 (by rw [e74, e78]; omega) (by decide)
  have a0s : arr s₃.mem L.Q 4 0 = arrQ s.mem L 0 := (qa2.trans qa3).arr0
  have a4s : arr s₃.mem L.Q 4 4 = kOf s.mem L sig := by
    rw [arr, Outside.val32 o3 (by rw [e74, e71]; omega) (by decide)]; exact v4
  have hbuf : Spec.Rsa.bytesAt s₃.mem L.Buf L.ql = Spec.Rsa.bytesAt s.mem L.Buf L.ql :=
    (qa2.trans qa3).bufBytes (by omega)
  -- The exponent's pointer and length, and `-q⁻¹`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrBuf_ok hL Q3.regs) fun s₄ ⟨⟨b12, b6, m4⟩, k4⟩ => ?_
  refine WP.mono (WP.keep [.r30, .r31] (Q := fun u => u.gpr .r30 = L.Buf ∧
      u.gpr .r31 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by prun [b12, b6, BitVec.add_zero]) (by decide))
    fun s₅ ⟨⟨c30, c31, m5⟩, k5⟩ => ?_
  have k35 := k4.trans k5
  have kk := k35
  have hs5 : Scr s₅ L.Q 1600 := Q3.inq.env.hs.congr k35.wr
  have h10 : s₅.gpr .r10 = off L.Q (slot 4 0) := (k35.gpr .r10 (by decide)).trans Q3.inq.env.h10
  have hm5 : s₅.mem = s₃.mem := by rw [m5, m4]
  have hodd : (word s₅.mem L.Q (slot 4 0)).toNat % 2 = 1 :=
    word_odd _ _ _ (2 * 4) (by decide) (by rw [hm5]; show arr s₃.mem L.Q 4 0 % 2 = 1; rw [a0s]; exact hqo)
  refine WP.mono (Pub.minv_ok hs5 h10 (by decide) hodd) fun s₆ ⟨⟨i12, inv, m6⟩, k6⟩ => ?_
  have k36 := k35.trans k6
  have hm6 : s₆.mem = s₃.mem := by rw [m6, hm5]
  rw [← m6] at inv
  have a1s : arr s₃.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := by
    rw [v1, a8s, h8]
  refine WP.seq (WP.mono (ModExp.powSecret_ok (hs5.congr k6.wr) (by decide) (by decide) (by decide)
    ((k6.gpr .r10 (by decide)).trans h10) ((k36.gpr .r29 (by decide)).trans Q3.inq.env.h29)
    ((k36.gpr .r11 (by decide)).trans Q3.inq.env.h11) i12 inv
    (by rw [hm6]; show 2 ≤ arr s₃.mem L.Q 4 0; rw [a0s]; exact hq2)
    (by rw [hm6]; show arr s₃.mem L.Q 4 0 % 2 = 1; rw [a0s]; exact hqo)
    (by rw [hm6]; show arr s₃.mem L.Q 4 1 < arr s₃.mem L.Q 4 0; rw [a1s, a0s]; exact Nat.mod_lt _ (by omega))
    (D := L.Buf) (L := L.ql)
    (show s₆.gpr .r30 = off L.Buf 0 by rw [k6.gpr .r30 (by decide), c30, off, BitVec.add_zero])
    ((k6.gpr .r31 (by decide)).trans c31)
    (by omega) (by omega)
    (fun i hi => by
      rw [k36.rd, k36.wr]
      exact (ScrL.bufN (s := s₃) Q3.scr hL (n := L.ql) (by omega)).ld (show i + 1 ≤ L.ql by omega))
    (buf_apartQ L (by omega))) fun s₇ ⟨⟨pw, o7⟩, k7⟩ => ?_)
  rw [hm6] at pw o7
  have qa7 : QArr L s₃.mem s₇.mem := QArr.of (outs_within o7 (lo := slot 4 1) (hi := slot 4 8)
    (by simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false]; intro r hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot_eq] <;> omega))
    (Nat.le_refl _) (by rw [e78, e71]; omega)
  have o7' : Outside L.Q (slot 4 1) (slot 4 8 - slot 4 1) s₃.mem s₇.mem := outs_within o7
    (by simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false]; intro r hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot_eq] <;> omega)
  refine WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₇.mem)
      (by prun [((k36.trans k7).gpr .r23 (by decide)).trans Q3.inq.h23, BitVec.add_zero]) (by decide))
    fun t ⟨⟨t31, mt⟩, kt⟩ => ?_
  have kall := ((((k1.trans k2).trans k3).trans k36).trans k7).trans kt
  refine ⟨⟨⟨⟨⟨h.inq.env.hs.congr kall.wr, (kt.gpr .r10 (by decide)).trans
      ((k7.gpr .r10 (by decide)).trans ((k6.gpr .r10 (by decide)).trans h10)),
      (kall.gpr .r29 (by decide)).trans h.inq.env.h29, (kall.gpr .r11 (by decide)).trans h.inq.env.h11, t31,
      by decide, by decide, by decide⟩, (kall.gpr .r21 (by decide)).trans h.inq.h21,
      (kall.gpr .r23 (by decide)).trans h.inq.h23⟩, h.scr.congr kall.wr,
      h.regs.keep kall⟩, ?_, ?_,
    by rw [mt]; exact qa2.trans (qa3.trans qa7), ?_⟩, kall.mono (by decide)⟩
  · rw [arrQ, mt]
    have rr : val32 s₃.mem L.Q (slot 4 1) (2 * 4) = 2 ^ (64 * 4) * 2 ^ (64 * 4) % val32 s₃.mem L.Q (slot 4 0) (2 * 4) := by
      rw [hRR]; exact a1s.trans (by rw [← a0s])
    show val32 s₇.mem L.Q (slot 4 4) (2 * 4) = _
    rw [pw rr, hbuf]
    show arr s₃.mem L.Q 4 4 ^ _ % arr s₃.mem L.Q 4 0 = _
    rw [a4s, a0s]
  · rw [arrQ, mt]
    show val32 s₇.mem L.Q (slot 4 8) (2 * 4) = _
    rw [Outside.val32 o7' (by rw [e78, e71]; omega) (by decide)]
    show arr s₃.mem L.Q 4 8 = _
    rw [arr, Outside.val32 o3 (by rw [e71, e78]; omega) (by decide)]
    exact a8s

  · rw [arrQ, mt]
    show val32 s₇.mem L.Q (slot 4 9) (2 * 4) = val32 s.mem L.Q (slot 4 9) (2 * 4)
    rw [Outside.val32 o7' (by simp only [slot_eq]; omega) (by decide),
      Outside.val32 o3 (by rw [e71]; simp only [slot_eq]; omega) (by decide),
      Outside.val32 o2 (by rw [e74]; simp only [slot_eq]; omega) (by decide)]

end VG.Proof.Dsa.PPC64LE
