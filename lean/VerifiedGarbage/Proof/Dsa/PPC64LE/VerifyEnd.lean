module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA verification on PPC64LE: the comparison

`compare_ok`: in the Q space, `v mod q` (`reduce` of the buffer's `p_len`
octets) compared with r, under the mask in the header's word `hMask`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

theorem mask_bit (c b : Bool) :
    mask c &&& mask b &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (if c = true ∧ b = true then 1 else 0) := by
  cases c <;> cases b <;> rfl

/-- The registers `compare` writes. -/
def cmpRegs : List Reg :=
  enterRegs ++ [.r30, .r31] ++ ModArith.redRegs ++ [.r5, .r8, .r9] ++ [.r6, .r12] ++ loadRegs ++
    eqRegs .r3 ++ [.r0, .r3, .r4]

/-- `compare`: `r3 := 1` if `v mod q = r` (`v` the buffer's `p_len` octets)
and `b` (the mask in `hMask`), else 0. -/
theorem compare_ok {s : State} {L : Lay} {key sig dig : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hsg : Src s L sig (2 * L.ql))
    (hq : 0 < arrQ s.mem L 0) (hm : word s.mem L.S hMask = mask b) :
    WP isa Verify.compare s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 =
          rOf s.mem L sig ∧ b = true then 1 else 0) ∧ Body L s.mem t.mem) ∧ Keep cmpRegs s t := by
  have hql := hL.ql
  have hpl := hL.pl
  have e71 : slot 4 1 = 304 := rfl
  have e75 : slot 4 5 = 496 := rfl
  unfold Verify.compare
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
  refine WP.seq (WP.mono (ModArith.reduce_ok (B := L.Q) (Z := 1600) (w := 4) (D := L.Buf) (L := L.pl) (e2.hs.congr k2.wr) (by decide) (by decide)
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
  have qa3 : QArr L s.mem s₃.mem := QArr.of o3' (by rw [e71]) (by rw [e71]; decide)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₃.mem)
      (by prun [((k2.trans k3).gpr .r23 (by decide)).trans q1.h23, BitVec.add_zero]) (by decide))
    fun s₄ ⟨⟨a31', m4⟩, k4⟩ => ?_
  have q4 : InQ s₄ L := ⟨⟨e2.hs.congr (k2.trans (k3.trans k4)).wr,
    ((k3.trans k4).gpr .r10 (by decide)).trans ((k2.gpr .r10 (by decide)).trans e2.h10),
    ((k2.trans (k3.trans k4)).gpr .r29 (by decide)).trans e2.h29,
    ((k2.trans (k3.trans k4)).gpr .r11 (by decide)).trans e2.h11, a31', by decide, by decide, by decide⟩,
    ((k2.trans (k3.trans k4)).gpr .r21 (by decide)).trans q1.h21,
    ((k2.trans (k3.trans k4)).gpr .r23 (by decide)).trans q1.h23⟩
  have Q4 : QS s₄ L key sig dig := ⟨q4, hs.congr (k13.trans k4).wr, hr.keep (k13.trans k4)⟩
  refine WP.mono (ptrR_ok Q4.regs) fun s₅ ⟨⟨b12, b6, m5⟩, k5⟩ => ?_
  have Q5 := Q4.step k5 (by decide)
  have k15 := (k13.trans k4).trans k5
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q5 hL (by decide) (by decide)
      ((hsg.keep k15.rd k15.wr).sub (o := 0) (k := L.ql) (by omega)) (by rw [b12, off, BitVec.add_zero]) b6
      (by omega) (by omega)) fun s₆ ⟨⟨Q6, v5, _, o6, qa6⟩, k6⟩ => ?_)
  refine WP.seq (WP.mono (eqMask_ok Q6.inq.env .r3 (a := 1) (b := 5) (by decide) (by decide))
    fun s₇ ⟨⟨c3, m7⟩, k7⟩ => ?_)
  have k17 := (k15.trans k6).trans k7
  refine WP.mono (WP.keep [.r0, .r3, .r4] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64
      (if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 = rOf s.mem L sig ∧ b = true
        then 1 else 0) ∧ u.mem = s₇.mem) ?_ (by decide))
    fun t ⟨⟨t3, mt⟩, kt⟩ => ⟨⟨t3, ?_⟩, (k17.trans kt).mono (by decide)⟩
  · have a1 : val32 s₆.mem L.Q (slot 4 1) (2 * 4) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 := by
      rw [Outside.val32 o6 (by rw [e71, e75]; omega) (by decide), m5, m4, v1]
    have a5 : val32 s₆.mem L.Q (slot 4 5) (2 * 4) = rOf s.mem L sig := by
      have := v5
      rw [arrQ, arr] at this
      rw [this, m5, m4, (hsg.sub (o := 0) (k := L.ql) (by omega)).bytes (qa3.qbody.body hL) hL.z256]
      simp only [rOf, off, BitVec.add_zero]
    have hb7 : Body L s.mem s₇.mem := by
      rw [m7]; exact (qa3.trans (by rw [← m4, ← m5]; exact qa6)).qbody.body hL
    have hv : s₇.mem.readW (L.S + BitVec.ofNat 64 0) 64 = mask b := by
      have := Outside.word hb7 (d := 0) (by omega) (by omega)
      rw [← hm]; exact this
    have hld : InRegions (s₇.rd ++ s₇.wr) (L.S + BitVec.ofNat 64 0) 8 :=
      (hs.congr (k17.wr)).ld (show 0 + 8 ≤ L.Z by have := hL.z256; omega)
    rw [a1, a5] at c3
    prun [c3, (k17.gpr .r21 (by decide)).trans hr.r21, hMask, hld, hv, mask_bit]
    simp only [decide_eq_true_eq]
  · rw [mt, m7]
    exact ((qa3.trans (by rw [← m4, ← m5]; exact qa6)).qbody.body hL)

end VG.Proof.Dsa.PPC64LE
