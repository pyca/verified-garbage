module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Gk
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.Dsa.PPC64LE.Range

/-!
# DSA key derivation on PPC64LE: x's range

`xRange_ok`: in the Q space with q in array 0, x (the `q_len` octets at
`r28`) into array 5, and `r20 :=` the mask in `r22` and'ed with the mask of
`0 < x < q`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The registers `xRange` writes. -/
def xRangeRegs : List Reg := enterRegs ++ [.r6, .r12] ++ loadRegs ++ inRangeRegs ++ [.r20]

/-- `xRange`: `r20 :=` the mask of `b` (in `r22`) and `0 < x < q`. Memory
changes only in the Q space's arrays from array 1 on. -/
theorem xRange_ok {s : State} {L : Lay} {key x out : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key x out) (hx : Src s L x L.ql) (h22 : s.gpr .r22 = mask b) :
    WP isa xRange s fun t =>
      (t.gpr .r20 = mask (b && decide (0 < kOf s.mem L x ∧ kOf s.mem L x < arrQ s.mem L 0)) ∧
        QS t L key x out ∧ QArr L s.mem t.mem) ∧ Keep xRangeRegs s t := by
  have hql := hL.ql
  have hn : slot 4 28 ≤ 2 ^ 64 := by decide
  unfold xRange
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  have Q1 : QS s₁ L key x out := ⟨q1, hs.congr k1.wr, hr.keep k1⟩
  refine WP.mono (ptrR_ok Q1.regs) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_
  have Q2 := Q1.step k2 (by decide)
  have k12 := k1.trans k2
  have m21 : s₂.mem = s.mem := m2.trans m1
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide) (by decide) (hx.keep k12.rd k12.wr) a12 a6
      (by omega) (by omega)) fun s₃ ⟨⟨Q3, v5, top5, o3, qa3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (zeroArr_ok Q3.inq.env (j := 7) (by decide)) fun s₄ ⟨⟨z7, o4⟩, k4⟩ => ?_)
  have qa4 : QArr L s₃.mem s₄.mem := QArr.of o4 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  have Q4 := Q3.step k4 (by decide)
  have e5 : arr s₄.mem L.Q 4 5 = kOf s.mem L x := by
    rw [arr, Outside.val32 o4 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)]
    rw [arrQ, arr] at v5; rw [v5, m21]; rfl
  have top5' : word s₄.mem L.Q (slot 4 5 + 8 * 4) = 0 := by
    rw [Outside.word o4 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)]; exact top5
  have qa : QArr L s.mem s₄.mem := by rw [← m21]; exact qa3.trans qa4
  have a0 : arr s₄.mem L.Q 4 0 = arrQ s.mem L 0 := qa.arr0
  have k14 := (k12.trans k3).trans k4
  refine WP.seq (WP.mono (inRange_ok Q4.inq.env (a := 5) (b := b) (by decide) (by decide) top5' z7
    ((k14.gpr .r22 (by decide)).trans h22)) fun s₅ ⟨⟨b22, o5⟩, k5⟩ => ?_)
  rw [e5, a0] at b22
  have qa5 : QArr L s₄.mem s₅.mem := QArr.of o5 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  have Q5 := Q4.step k5 (by decide)
  refine WP.mono (WP.keep [.r20] (Q := fun t => t.gpr .r20 = s₅.gpr .r22 ∧ t.mem = s₅.mem)
    (by prun [BitVec.add_zero]) (by decide)) fun t ⟨⟨t20, mt⟩, kt⟩ => ?_
  exact ⟨⟨t20.trans b22, Q5.step kt (by decide), by rw [mt]; exact qa.trans qa5⟩,
    ((k14.trans k5).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE
