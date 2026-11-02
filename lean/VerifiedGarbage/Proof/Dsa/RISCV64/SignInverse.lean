module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyInv
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on RISC-V: k's inverse

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Inverse.lean`). `inverseK_ok`:
verification's `inverse_ok` (`VerifyInv.lean`) with the base k, the nonce at
`ra`, in place of s.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
  VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)

theorem inverseK_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig) (hi : QInv s L)
    (hsg : Src s L sig L.ql) (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h24 : arrQ s.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0) :
    WP isa inverseK s fun t =>
      (QS t L key sig ∧ QInv t L ∧
        arrQ t.mem L 4 = kOf s.mem L sig ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) %
          arrQ s.mem L 0 ∧
        (∀ j < 28, 24 ≤ j → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧ Keep invRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e28 := e 28
  unfold inverseK
  refine WP.seq (WP.mono (ptrR_ok h.scr hL h.regs) fun s₁ ⟨⟨a7, a8, m1⟩, k1⟩ => ?_)
  have Q1 := h.stepM k1 m1
  refine WP.seq (WP.mono (loadQ_ok (j := 4) Q1 hL (by decide)
      (hsg.keep k1.2.1 k1.2.2) a7 a8 (by omega) (by omega))
    fun s₂ ⟨⟨Q2, v4, _, o2⟩, k2⟩ => ?_)
  rw [m1] at v4 o2
  refine WP.seq (WP.mono (copy_ok Q2.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨c1, o3⟩, k3⟩ => ?_)
  have Q3 := Q2.step k3 (Body.ofQ hL o3 (by omega))
  have A0 : arrQ s₃.mem L 0 = arrQ s.mem L 0 := by
    rw [arrQ, o3.wordsVal (by omega) (by omega_arith), o2.wordsVal (by omega) (by omega_arith)]
  have W0 : word s₃.mem L.Q (slot L.wq 0) = word s.mem L.Q (slot L.wq 0) := by
    rw [o3.word (by omega) (by omega_arith), o2.word (by omega) (by omega_arith)]
  have A4 : arrQ s₃.mem L 4 = kOf s.mem L sig := by
    rw [arrQ, o3.wordsVal (by omega) (by omega_arith)]; exact v4
  have A24 : ∀ j < 28, 24 ≤ j → arrQ s₃.mem L j = arrQ s.mem L j := fun j hj hj24 => by
    have := slot_lt (w := L.wq) hj
    have := slot_mono (w := L.wq) hj24
    rw [arrQ, o3.wordsVal (by omega) (by omega_arith), o2.wordsVal (by omega) (by omega_arith)]
  have A1 : arrQ s₃.mem L 1 = 2 ^ (128 * L.wq) % arrQ s.mem L 0 := by
    rw [arrQ, wordsVal_congr (m := s₂.mem) (d := slot L.wq 24) fun i hi => c1 i (by omega)]
    rw [← h24, arrQ, o2.wordsVal (by omega) (by omega_arith)]
  have hbuf : Spec.Rsa.bytesAt s₃.mem L.Buf L.ql = Spec.Rsa.bytesAt s.mem L.Buf L.ql := by
    have qa : QArr L s.mem s₃.mem :=
      (QArr.of o2 (by omega) (by omega)).trans (QArr.of o3 (by omega) (by omega))
    exact qa.bufBytes hL (by omega)
  -- The exponent's pointer and length.
  refine WP.seq (WP.block_append (WP.mono (ptrBuf_ok Q3.scr hL Q3.regs) fun s₄ ⟨⟨b7, b8, m4⟩, k4⟩ =>
    WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off L.Buf 0 ∧
      u.gpr .s10 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by brun [b7, b8, BitVec.add_zero]) (by decide) (by rfl))
    fun s₅ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_))
  have k35 := k4.trans k5
  have m53 : s₅.mem = s₃.mem := by rw [m5, m4]
  have e5 := Q3.inq.env.keep k35
  have k15 := (((k1.trans k2).trans k3).trans k35)
  refine WP.mono (Win.powWin_ok (D := L.Buf) (L := L.ql) e5.hs (by omega) (by omega)
    (by omega) e5.a7 e5.s5 e5.t0
    (by rw [m53, W0, k15.gpr (by decide)]; exact hi)
    (by rw [m53]; show 2 ≤ arrQ s₃.mem L 0; rw [A0]; exact hq2)
    (by rw [m53]; show arrQ s₃.mem L 0 % 2 = 1; rw [A0]; exact hqo)
    (by rw [m53]; show arrQ s₃.mem L 1 < arrQ s₃.mem L 0; rw [A1, A0]; exact Nat.mod_lt _ (by omega))
    c9 c10 (by omega) (by omega_arith)
    (fun i hi => by
      rw [k35.2.1, k35.2.2]
      exact (ScrL.bufN (s := s₃) Q3.scr hL (n := L.ql) (by rcases hL.pl with e | e | e <;> omega)).ld
        (show i + 1 ≤ L.ql by omega))
    (buf_apartQ L (by omega))) fun t ⟨⟨r4, o4'⟩, k6⟩ => ?_
  have o4 : Outside L.Q (slot L.wq 1) (23 * (8 * (L.wq + 2))) s₃.mem t.mem := by rw [← m53]; exact o4'
  rw [m53] at r4
  have r4 := r4 (by
    show arrQ s₃.mem L 1 = 2 ^ (64 * L.wq) * 2 ^ (64 * L.wq) % arrQ s₃.mem L 0
    rw [A1, A0, pow_two_mul])
  rw [hbuf] at r4
  have qa : QArr L s.mem t.mem :=
    ((QArr.of o2 (by omega) (by omega)).trans (QArr.of o3 (by omega) (by omega))).trans
      (QArr.of o4 (by omega) (by omega))
  refine ⟨⟨Q3.step (k35.trans k6) (Body.ofQ hL o4 (by omega)), ?_, ?_, fun j hj hj24 => ?_, qa⟩,
    (k15.trans k6).mono (by decide)⟩
  · show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o4.word (by omega) (by omega_arith), W0, (k15.trans k6).gpr (by decide)]; exact hi
  · show wordsVal t.mem L.Q (slot L.wq 4) L.wq = _
    rw [r4]
    show arrQ s₃.mem L 4 ^ _ % arrQ s₃.mem L 0 = _
    rw [A4, A0]
  · have := slot_lt (w := L.wq) hj
    have := slot_mono (w := L.wq) hj24
    rw [arrQ, o4.wordsVal (by omega) (by omega_arith)]; exact A24 j hj hj24

end VG.Proof.Dsa.RISCV64
