module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtAdd

/-!
# DSA on PPC64LE: v modulo q by Montgomery multiplications

`vModQ_ok`: `v mod q` into the Q space's array 4, for `v` in the P space's
array 6, by `Crt.reduceFrom` (`Crt.reduceFrom_ok`) in the Q space, whose array 0
`r23` gives (`r21` holds `S`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- `redPtrs`: the P space's array 6 into `r30` and its `w` words into `r31`. -/
theorem redPtrs_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hr : Regs s L key sig dig) :
    WP isa (.block Verify.redPtrs) s fun t =>
      (t.gpr .r30 = off L.S (slot L.wp 6) ∧ t.gpr .r31 = BitVec.ofNat 64 L.wp ∧ t.mem = s.mem) ∧
        Keep [.r0, .r30, .r31] s t := by
  have hw8 := hL.wp_eq
  refine WP.keep _ ?_ (by decide)
  unfold Verify.redPtrs getP
  have hpl := hL.pl
  prun [hr.r21, hr.p_eq, hdrBytes, BitVec.add_zero]
  refine ⟨?_, ?_⟩
  · have e : (BitVec.ofNat 64 L.pl + 16#64) * 6#64 + 256#64 = BitVec.ofNat 64 (slot L.wp 6) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Lay.slot_eq]
      omega_arith
    rw [off, ← e]
    ac_rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith

/-- The registers `vModQ` writes. -/
def vModRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
    .r22, .r23, .r24, .r29, .r30, .r31]

/-- `vModQ`: `v mod q` into the Q space's array 4, for `v` in the P space's
array 6, q (odd) in the Q space's array 0 and `R² mod q` in its array 1; memory
changes only in the Q space's first `slot 4 24` octets, where arrays 0 and 1
are kept. -/
theorem vModQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h1 : arrQ s.mem L 1 = 2 ^ (128 * 4) % arrQ s.mem L 0) :
    WP isa Verify.vModQ s fun t =>
      (InQ t L ∧ Regs t L key sig dig ∧ arrQ t.mem L 4 = arrP s.mem L 6 % arrQ s.mem L 0 ∧
        arrQ t.mem L 0 = arrQ s.mem L 0 ∧ arrQ t.mem L 1 = arrQ s.mem L 1 ∧
        Outside L.S L.qOff (slot 4 24) s.mem t.mem) ∧ Keep vModRegs s t := by
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hbe := hL.buf_end
  have hpl := hL.pl
  unfold Verify.vModQ Verify.redEnter
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  have hr1 := hr.keep k1 (by decide)
  refine WP.mono (redPtrs_ok hL hr1) fun s₂ ⟨⟨a30, a31, m2⟩, k2⟩ => ?_
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  have h10₂ : s₂.gpr .r10 = off L.Q (slot 4 0) := (k2.gpr .r10 (by decide)).trans q1.env.h10
  have hlow : (word s₂.mem L.Q (slot 4 0)).toNat % 2 = 1 := by
    have h1' := word_eq_w32 s₂.mem L.Q (slot 4 0)
    have h2 : val32 s₂.mem L.Q (slot 4 0) (7 + 1) =
        w32 s₂.mem L.Q (slot 4 0) + 2 ^ 32 * val32 s₂.mem L.Q (slot 4 0 + 4) 7 := rfl
    have h3 : val32 s₂.mem L.Q (slot 4 0) (7 + 1) = arrQ s.mem L 0 := by rw [hm2]
    omega_arith
  refine WP.mono (Pub.minv_ok (q1.env.hs.congr k2.wr) h10₂ (by decide) hlow) fun s₃ ⟨⟨r12lt, r12inv, m3⟩, k3⟩ => ?_
  have hm3 : s₃.mem = s.mem := by rw [m3, hm2]
  have k13 := (k1.trans k2).trans k3
  have hn : 4 * Crt.nChunks L.wp 4 = L.wp := by
    simp only [Crt.nChunks]; rcases hpl with h | h | h <;> omega_arith
  have h30₃ : s₃.gpr .r30 = off L.S (slot L.wp 6) := (k3.gpr .r30 (by decide)).trans a30
  have h31₃ : s₃.gpr .r31 = BitVec.ofNat 64 L.wp := (k3.gpr .r31 (by decide)).trans a31
  refine WP.seq (WP.mono (Crt.reduceFrom_ok (BX := L.S) (Z := L.Z) (oA := L.qOff) (w := 4) (wX := L.wp) (K := L.wp)
      (Pv := arrQ s.mem L 0) (Cv := arrP s.mem L 6) (Hb := fun t => t.gpr .r23 = off L.S L.qOff)
      (hs.congr k13.wr) (by simp only [Lay.bOff] at hbe; have : slot 4 24 = 1408 := rfl; omega_arith)
      (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith) (by decide) (by decide) (by omega_arith)
      (by omega_arith) (by omega_arith)
      ((k3.gpr .r10 (by decide)).trans h10₂) (((k2.trans k3).gpr .r23 (by decide)).trans q1.h23)
      (fun _ _ h k => (k.gpr .r23 (by decide)).trans h)
      (fun t h => WP.keep [.r10] (Q := fun u => u.gpr .r10 = off (off L.S L.qOff) (slot 4 0) ∧ u.mem = t.mem)
        (by prun [h, hdrBytes]; rw [off, show slot 4 0 = 256 from rfl]) (by decide))
      (fun t kt => WP.keep [.r30, .r31] (Q := fun u => u.gpr .r30 = off L.S (slot L.wp 6) ∧
          u.gpr .r31 = BitVec.ofNat 64 L.wp ∧ u.mem = t.mem)
        (by prun [(kt.gpr .r30 (by decide)).trans h30₃, (kt.gpr .r31 (by decide)).trans h31₃]) (by decide))
      (((k2.trans k3).gpr .r29 (by decide)).trans q1.env.h29) (((k2.trans k3).gpr .r11 (by decide)).trans q1.env.h11)
      r12lt (by rw [m3]; exact r12inv) (by rw [hm3]) hq2 hqo (by rw [hm3]; exact h1)
      (by rw [hm3, hn, ← Pre.val32_eq_wv]))
    fun s₄ ⟨⟨v4, p0, p1, _, _, o4, a10, _⟩, k4⟩ => ?_)
  have g23 : s₄.gpr .r23 = L.Q :=
    (k4.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans q1.h23))
  refine WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₄.mem)
    (by unfold Verify.redExit; prun [g23, BitVec.add_zero]) (by decide)) fun t ⟨⟨t31, mt⟩, kt⟩ => ?_
  have t21 : t.gpr .r21 = L.S := (((k13.trans k4).trans kt).gpr .r21 (by decide)).trans hr.r21
  have K := (k13.trans k4).trans kt
  rw [hm3] at o4
  refine ⟨⟨⟨⟨q1.env.hs.congr ((k2.trans k3).trans (k4.trans kt)).wr, (kt.gpr .r10 (by decide)).trans a10,
      (((k2.trans k3).trans (k4.trans kt)).gpr .r29 (by decide)).trans q1.env.h29,
      (((k2.trans k3).trans (k4.trans kt)).gpr .r11 (by decide)).trans q1.env.h11, t31, by decide, by decide, by decide⟩, t21, (kt.gpr .r23 (by decide)).trans g23⟩,
    ⟨t21, (K.gpr .r27 (by decide)).trans hr.r27, (K.gpr .r28 (by decide)).trans hr.r28,
      (K.gpr .r26 (by decide)).trans hr.r26, by rw [K.gpr .r2 (by decide)]; exact hr.pl,
      by rw [K.gpr .r2 (by decide)]; exact hr.ql⟩,
    by rw [arrQ, arr, mt]; exact v4, by rw [arrQ, arr, mt]; exact p0, by rw [arrQ, arr, mt]; exact p1.trans h1.symm,
    by rw [mt]; exact o4⟩, K.mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE
