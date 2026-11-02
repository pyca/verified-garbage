module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA key derivation on RISC-V: x's range

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/X.lean`). `xRange_ok`: into the Q
space, x (the `q_len` octets at `ra`) into array 5, and `a4 &=` the mask of
`0 < x < q`, q in array 0.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- The registers `xRange` writes. -/
def xRangeRegs : List Reg := enterRegs ++ [.s7, .s8] ++ loadRegs ++ [.s0, .t3, .t5] ++ inRangeRegs

/-- `xRange`: `a4 &=` the mask of `0 < x < q`. Memory changes only in the
Q space's arrays from array 1 on. -/
theorem xRange_ok {s : State} {L : Lay} {key x : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key x) (hx : Src s L x L.ql) (h4 : s.gpr .a4 = mask b) :
    WP isa xRange s fun t =>
      (t.gpr .a4 = mask (b && decide (0 < kOf s.mem L x ∧ kOf s.mem L x < arrQ s.mem L 0)) ∧
        QS t L key x ∧ QArr L s.mem t.mem) ∧ Keep xRangeRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  have e7 := e 7; have e8 := e 8; have e28 := e 28
  unfold xRange
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  have Q1 : QS s₁ L key x := ⟨q1, hs.congr k1.2.2, hr.keepM k1 m1⟩
  refine WP.mono (ptrR_ok Q1.scr hL Q1.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_
  have Q2 := Q1.stepM k2 m2
  have k12 := k1.trans k2
  have m21 : s₂.mem = s.mem := m2.trans m1
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide) (hx.keep k12.2.1 k12.2.2) a7 a8
      (by omega) (by omega)) fun s₃ ⟨⟨Q3, v5, top5, o3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (zeroArr_ok Q3.inq.env (j := 7) (by decide)) fun s₄ ⟨⟨z7, o4⟩, k4⟩ => ?_)
  have Q4 := Q3.step k4 (Body.ofQ hL o4 (by omega))
  have k14 := (k12.trans k3).trans k4
  have e5' : wordsVal s₄.mem L.Q (slot L.wq 5) L.wq = kOf s.mem L x := by
    rw [o4.wordsVal (by omega) (by omega_arith)]
    refine v5.trans ?_
    rw [m21]; rfl
  have e0' : wordsVal s₄.mem L.Q (slot L.wq 0) L.wq = arrQ s.mem L 0 := by
    rw [o4.wordsVal (by omega) (by omega_arith), o3.wordsVal (by omega) (by omega_arith), m21]
  have top5' : word s₄.mem L.Q (slot L.wq 5 + 8 * L.wq) = 0 := by
    rw [o4.word (by omega) (by omega_arith)]; exact top5
  refine WP.mono (inRange_ok Q4.inq.env (a := 5) (b := b) (by decide) (by decide) (by decide)
    top5' z7 ((k14.gpr (by decide)).trans h4)) fun t ⟨⟨c4, o5⟩, k5⟩ => ?_
  rw [e5', e0'] at c4
  have qa : QArr L s.mem t.mem := by
    have qa1 : QArr L s₂.mem s₃.mem := QArr.of o3 (by omega) (by omega)
    have qa2 : QArr L s₃.mem s₄.mem := QArr.of o4 (by omega) (by omega)
    have qa3 : QArr L s₄.mem t.mem := QArr.of o5 (by omega) (by omega)
    rw [← m21]; exact (qa1.trans qa2).trans qa3
  exact ⟨⟨c4, Q4.step k5 (Body.ofQ hL o5 (by omega)), qa⟩, (k14.trans k5).mono (by decide)⟩

end VG.Proof.Dsa.RISCV64
