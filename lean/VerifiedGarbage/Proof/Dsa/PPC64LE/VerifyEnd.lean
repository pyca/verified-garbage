module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Dsa.PPC64LE.ReduceQ
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr

/-!
# DSA verification on PPC64LE: the comparison

`compare_ok`: `v mod q` (`vModQ_ok`, from the P space's array 4) compared
with r, under the mask in the header's word `hMask`.
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
  copyRegs ++ vModRegs ++ [.r5, .r8, .r9] ++ [.r6, .r12] ++ loadRegs ++ eqRegs .r3 ++ [.r0, .r3, .r4]

/-- `compare`, in the P space with `V` in its array 4, q (odd) in the Q space's
array 0 and `R² mod q` in its array 1: `r3 := 1` if `V mod q = r` and `b`
(the mask in `hMask`), else 0. -/
theorem compare_ok {s : State} {L : Lay} {key sig dig : Addr} {b : Bool} {V : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hsg : Src s L sig (2 * L.ql)) (hP : InP s L)
    (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) (h1 : arrQ s.mem L 1 = 2 ^ (128 * 4) % arrQ s.mem L 0)
    (hv : arrP s.mem L 4 = V) (hm : word s.mem L.S hMask = mask b) :
    WP isa Verify.compare s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if V % arrQ s.mem L 0 = rOf s.mem L sig ∧ b = true then 1 else 0) ∧
        Body L s.mem t.mem) ∧ Keep cmpRegs s t := by
  have hql := hL.ql
  have hpl := hL.pl
  have hw := hL.wp_ge
  have hbe := hL.buf_end
  have hnw := hL.nowrap
  have e74 : slot 4 4 = 448 := rfl
  have e75 : slot 4 5 = 496 := rfl
  unfold Verify.compare
  -- v into the P space's array 6.
  refine WP.seq (WP.mono (copy_ok hP.env (o := 6) (a := 4) (by decide) (by decide) (by decide))
    fun s₁ ⟨⟨v6, o1⟩, k1⟩ => ?_)
  have B1 : Body L s.mem s₁.mem := Body.ofP hL o1 (by simp only [Lay.slot_eq]; omega_arith)
    (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)
  have pb1 : PBody L s.mem s₁.mem := o1.mono (by simp only [Lay.slot_eq]; omega_arith)
    (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)
  have aq : ∀ j < 28, arrQ s₁.mem L j = arrQ s.mem L j := fun j hj => pb1.arrQ hL j hj
  -- `v mod q` into the Q space's array 4.
  refine WP.seq (WP.mono (vModQ_ok hL (hs.congr k1.wr) (hr.keep k1 (by decide)) (by rw [aq 0 (by decide)]; exact hq2)
      (by rw [aq 0 (by decide)]; exact hqo) (by rw [aq 1 (by decide), aq 0 (by decide)]; exact h1))
    fun s₂ ⟨⟨q2, r2, a4, a0, _, o2⟩, k2⟩ => ?_)
  rw [aq 0 (by decide)] at a4 a0
  have v6' : arrP s₁.mem L 6 = V := v6.trans hv
  rw [v6'] at a4
  have B2 : Body L s₁.mem s₂.mem := o2.mono (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)
    (by simp only [Lay.bOff, Lay.qOff] at hbe ⊢; have : slot 4 24 = 1408 := rfl; omega_arith)
  have B12 := B1.trans B2
  have k12 := k1.trans k2
  have Q2 : QS s₂ L key sig dig := ⟨q2, hs.congr k12.wr, r2⟩
  refine WP.seq (WP.mono (ptrR_ok Q2.regs) fun s₃ ⟨⟨b12, b6, m3⟩, k3⟩ => ?_)
  have Q3 := Q2.step k3 (by decide)
  have k13 := k12.trans k3
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q3 hL (by decide) (by decide)
      ((hsg.keep k13.rd k13.wr).sub (o := 0) (k := L.ql) (by omega_arith)) (by rw [b12, off, BitVec.add_zero]) b6
      (by omega_arith) (by omega_arith)) fun s₄ ⟨⟨Q4, v5, _, o4, qa4⟩, k4⟩ => ?_)
  refine WP.seq (WP.mono (eqMask_ok Q4.inq.env .r3 (a := 4) (b := 5) (by decide) (by decide))
    fun s₅ ⟨⟨c3, m5⟩, k5⟩ => ?_)
  have k15 := (k13.trans k4).trans k5
  refine WP.mono (WP.keep [.r0, .r3, .r4] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64
      (if V % arrQ s.mem L 0 = rOf s.mem L sig ∧ b = true then 1 else 0) ∧ u.mem = s₅.mem) ?_ (by decide))
    fun t ⟨⟨t3, mt⟩, kt⟩ => ⟨⟨t3, ?_⟩, (k15.trans kt).mono (by decide)⟩
  · have a1 : val32 s₄.mem L.Q (slot 4 4) (2 * 4) = V % arrQ s.mem L 0 := by
      rw [Outside.val32 o4 (by rw [e74, e75]; omega_arith) (by decide), m3]; exact a4
    have a5 : val32 s₄.mem L.Q (slot 4 5) (2 * 4) = rOf s.mem L sig := by
      have := v5
      rw [arrQ, arr] at this
      rw [this, m3, (hsg.sub (o := 0) (k := L.ql) (by omega_arith)).bytes B12 hL.z256]
      simp only [rOf, off, BitVec.add_zero]
    have hb5 : Body L s.mem s₅.mem := by
      rw [m5]; exact B12.trans (by rw [← m3]; exact qa4.qbody.body hL)
    have hv' : s₅.mem.readW (L.S + BitVec.ofNat 64 0) 64 = mask b := by
      have := Outside.word hb5 (d := 0) (by omega_arith) (by omega_arith)
      rw [← hm]; exact this
    have hld : InRegions (s₅.rd ++ s₅.wr) (L.S + BitVec.ofNat 64 0) 8 :=
      (hs.congr (k15.wr)).ld (show 0 + 8 ≤ L.Z by have := hL.z256; omega_arith)
    rw [a1, a5] at c3
    prun [c3, (k15.gpr .r21 (by decide)).trans hr.r21, hMask, hld, hv', mask_bit]
    simp only [decide_eq_true_eq]
  · rw [mt, m5]
    exact B12.trans (by rw [← m3]; exact qa4.qbody.body hL)

end VG.Proof.Dsa.PPC64LE
