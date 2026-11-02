module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyQ
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: the comparison

As on PPC64LE (`Proof/Dsa/PPC64LE/VerifyEnd.lean`). `compare_ok`: in the Q
space, `v mod q` (`reduce64` of the buffer's `p_len` octets) compared with
r, under the mask in the header's `hMask`: `a0 := 1` exactly when they are
equal and the mask is all ones.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

theorem mask_bit (c b : Bool) :
    mask c &&& mask b &&& 1#64 = BitVec.ofNat 64 (if c = true ∧ b = true then 1 else 0) := by
  cases c <;> cases b <;> rfl

/-- The registers `compare` writes. -/
def cmpRegs : List Reg :=
  enterRegs ++ [.s9, .t2, .s10] ++ ModArith.redRegs ++ [.a2, .a5, .a6] ++ [.s7, .s8] ++ loadRegs ++
    eqRegs .a0 ++ [.a0, .a1]

/-- `compare`: `a0 := 1` if `v mod q = r` (`v` the buffer's `p_len` octets)
and `b` (the mask in `hMask`), else 0. -/
theorem compare_ok {s : State} {L : Lay} {key sig : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hsg : Src s L sig (2 * L.ql))
    (hq : 0 < arrQ s.mem L 0) (hm : word s.mem L.S hMask = mask b) :
    WP isa Verify.compare s fun t =>
      (t.gpr .a0 = BitVec.ofNat 64 (if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 =
          rOf s.mem L sig ∧ b = true then 1 else 0) ∧ Body L s.mem t.mem) ∧ Keep cmpRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hZ := hL.z256
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  have e0 := Lay.slot_eq L.wq 0; have e1 := Lay.slot_eq L.wq 1; have e4 := Lay.slot_eq L.wq 4
  have e5 := Lay.slot_eq L.wq 5
  unfold Verify.compare
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  refine WP.mono (bufBase_ok (hs.congr k1.2.2) hL (hr.keepM k1 m1) (rd := .s9) (t := .t2) (by decide) (by decide)
    (by decide)) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_
  refine WP.mono (getP_ok (hs.congr (k1.trans k2).2.2) hL (hr.keepM (k1.trans k2) (by rw [m2, m1])) .s10)
    fun s₃ ⟨⟨a10, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have m31 : s₃.mem = s.mem := by rw [m3, m2, m1]
  have e3 := q1.env.keep (k2.trans k3)
  refine WP.seq (WP.mono (ModArith.reduce64_ok (D := L.Buf) (L := L.pl) e3.hs (by omega) (by omega)
    (by omega) e3.a7 e3.s5 e3.t0 (by rw [m31]; exact hq)
    (by rw [k3.gpr (by decide), a9]; exact (BitVec.add_zero _).symm) a10 (by omega) (by omega_arith)
    (fun i hi => by
      rw [k13.2.1, k13.2.2]
      exact (ScrL.bufN hs hL (n := L.pl) (by omega)).ld (show i + 1 ≤ L.pl by omega))
    (buf_apartQ L (by omega))) fun s₄ ⟨⟨v1, o4⟩, k4⟩ => ?_)
  rw [m31] at v1 o4
  have hb4 : Body L s.mem s₄.mem := Body.ofQ hL o4 (by omega)
  have Q4 : QS s₄ L key sig := ⟨⟨e3.keep k4, ((k2.trans k3).trans k4 |>.gpr (by decide)).trans q1.s6⟩,
    hs.congr (k13.trans k4).2.2, hr.keep (k13.trans k4) hb4⟩
  refine WP.seq (WP.mono (ptrR_ok Q4.scr hL Q4.regs) fun s₅ ⟨⟨b7, b8, m5⟩, k5⟩ => ?_)
  have Q5 := Q4.stepM k5 m5
  have k15 := (k13.trans k4).trans k5
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q5 hL (by decide)
      ((hsg.keep k15.2.1 k15.2.2).sub (o := 0) (k := L.ql) (by omega)) (by rw [b7, off, BitVec.add_zero]) b8
      (by omega) (by omega)) fun s₆ ⟨⟨Q6, v5, _, o6⟩, k6⟩ => ?_)
  refine WP.seq (WP.mono (eqMask_ok Q6.inq.env (j := 1) (k := 5) (rd := .a0) (by decide) (by decide) (by decide))
    fun s₇ ⟨⟨c0, m7⟩, k7⟩ => ?_)
  have k17 := (k15.trans k6).trans k7
  have hb6 : Body L s.mem s₆.mem := hb4.trans (by rw [← m5]; exact Body.ofQ hL o6 (by omega))
  have a1 : wordsVal s₆.mem L.Q (slot L.wq 1) L.wq =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 := by
    rw [o6.wordsVal (by omega) (by omega_arith), m5, v1]
  have a5 : wordsVal s₆.mem L.Q (slot L.wq 5) L.wq = rOf s.mem L sig := by
    refine v5.trans ?_
    rw [m5, (hsg.sub (o := 0) (k := L.ql) (by omega)).bytes hb4 (by omega)]
    simp only [rOf, off, BitVec.add_zero]
  rw [a1, a5] at c0
  have hb7 : Body L s.mem s₇.mem := by rw [m7]; exact hb6
  obtain ⟨hin, hal⟩ := ScrL.hdr (hs.congr k17.2.2) hL (d := 0) (by decide) (by decide)
  have hv : word s₇.mem L.S hMask = mask b := by rw [hb7.word (by decide)]; exact hm
  refine WP.mono (WP.keep [.a0, .a1] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64
      (if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 = rOf s.mem L sig ∧ b = true
        then 1 else 0) ∧ u.mem = s₇.mem) ?_ (by decide) (by rfl))
    fun t ⟨⟨t0, mt⟩, kt⟩ => ⟨⟨t0, by rw [mt]; exact hb7⟩, (k17.trans kt).mono (by decide)⟩
  have hv' : s₇.mem.readW (off L.S 0) 64 = mask b := hv
  brun [c0, (k17.gpr (r := .s6) (by decide)).trans hr.s6, hMask, hin, hal, hv']
  rw [mask_bit]
  simp only [decide_eq_true_eq]

end VG.Proof.Dsa.RISCV64
