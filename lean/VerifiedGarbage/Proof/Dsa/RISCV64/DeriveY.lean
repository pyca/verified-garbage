module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA key derivation on RISC-V: y

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/Y.lean`). `yValue_ok`: in the P
space with p in array 0 and `R² mod p` in array 24, `y = g^x mod p` (x the
`q_len` octets at `ra`) to the buffer's first `p_len` octets, and `a4 :=`
the mask of `y ≠ 0` and `y ≠ 1`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- The registers `yValue` writes. -/
def yValueRegs : List Reg :=
  [.s9] ++ ptrRegs ++ powPRegs ++ [.s0, .t3, .t5] ++ [.a4] ++ nonZeroRegs ++ [.s0, .t3, .t5] ++ nonZeroRegs ++
    [.s7, .t2] ++ [.s8] ++ storeRegs

theorem yv_b1 (L : Lay) : 256 ≤ slot L.wp 1 ∧ slot L.wp 1 + 23 * (8 * (L.wp + 2)) ≤ L.qOff := by
  simp only [Lay.qOff, Lay.slot_eq]; omega

theorem yv_b7 (L : Lay) : 256 ≤ slot L.wp 7 ∧ slot L.wp 7 + 8 * L.wp ≤ L.qOff ∧ slot L.wp 8 ≤ L.qOff := by
  simp only [Lay.qOff, Lay.slot_eq]; omega

/-- `yValue`: `y = g^x mod p` to the buffer's first `p_len` octets, and
`a4 :=` the mask of `y ≠ 0` and `y ≠ 1`. Memory changes only in the P
space's arrays and the buffer's first `p_len` octets. -/
theorem yValue_ok {s : State} {L : Lay} {key x : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key x) (hin : InP s L) (hi : PInv s L) (hk : Src s L key (2 * L.pl + L.ql))
    (hx : Src s L x L.ql) (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1)
    (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa yValue s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) = gOf s.mem L key ^ kOf s.mem L x % p ∧
        t.gpr .a4 = mask (decide (gOf s.mem L key ^ kOf s.mem L x % p ≠ 0) &&
          decide (gOf s.mem L key ^ kOf s.mem L x % p ≠ 1)) ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem) ∧
        Keep yValueRegs s t := by
  have hpb : L.pl ≤ 2 ^ 64 - 1600 := by rcases hL.pl with e | e | e <;> rw [e] <;> decide
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hpl := hL.pl
  have hbe := hL.buf_end
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e1 := e 1; have e4 := e 4; have e7 := e 7; have e24 := e 24; have e28 := e 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold yValue
  -- The pointers: x into `s9`, g's octets into `s7`.
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = x ∧ u.mem = s.mem)
    (by brun [hr.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ =>
    WP.mono (ptrG_ok (hs.congr k1.2.2) hL (hr.keepM k1 m1)) fun s₂ ⟨⟨b7, _, m2⟩, k2⟩ => ?_))
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  -- `g^x mod p` into array 4.
  refine WP.seq (WP.mono (powSrc_ok (N := off key (L.pl + L.ql)) (E := x) (p := p) hL (hs.congr k12.2.2)
      (hr.keepM k12 hm2) (hin.keep k12) (by
        show ((word s₂.mem L.S (slot L.wp 0)).toNat * (s₂.gpr .t1).toNat + 1) % 2 ^ 64 = 0
        rw [hm2, k12.gpr (by decide)]; exact hi)
      ((hk.keep k12.2.1 k12.2.2).sub (o := L.pl + L.ql) (k := L.pl) (by omega)) b7 (hx.keep k12.2.1 k12.2.2)
      ((k2.gpr (by decide)).trans a9) (by rw [hm2]; exact hp0) hp hpo (by rw [hm2]; exact hrr))
    fun s₃ ⟨⟨v4, in3, _, o3⟩, k3⟩ => ?_)
  rw [hm2] at v4 o3
  have k13 := k12.trans k3
  have y4 : arrP s₃.mem L 4 = gOf s.mem L key ^ kOf s.mem L x % p := v4
  have hyp : gOf s.mem L key ^ kOf s.mem L x % p < p := Nat.mod_lt _ (by omega)
  generalize gOf s.mem L key ^ kOf s.mem L x % p = y at y4 hyp ⊢
  -- 0 into array 7, `a4 :=` all ones.
  refine WP.seq (WP.mono (zeroArr_ok in3.env (j := 7) (by decide)) fun s₄ ⟨⟨z7, o4⟩, k4⟩ => ?_)
  have en4 := in3.env.keep k4
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask true ∧ u.mem = s₄.mem)
    (by brun [exec_li (show imm12 (-1) by decide)]; rfl) (by decide) (by rfl)) fun s₅ ⟨⟨a4, m5⟩, k5⟩ => ?_)
  have en5 := en4.keep k5
  have y5 : arrP s₅.mem L 4 = y := by
    rw [arrP, m5, o4.wordsVal (by omega) (by omega_arith)]; exact y4
  -- `a4 &=` the masks of `y ≠ 0` and `y ≠ 1`.
  refine WP.seq (WP.mono (nonZero_ok en5 (a := 4) (c := 0) (by decide) (by rw [m5]; exact z7) a4)
    fun s₆ ⟨⟨b4, m6⟩, k6⟩ => ?_)
  rw [show wordsVal s₅.mem L.S (slot L.wp 4) L.wp = y from y5] at b4
  have en6 := en5.keep k6
  refine WP.seq (WP.mono (Pub.oneP_ok en6.hs (by omega) (by omega) (yv_b7 L).2.2 en6.a7 en6.s5 en6.t0)
    fun s₇ ⟨⟨v7, o7'⟩, k7⟩ => ?_)
  have o7 : Outside L.S (slot L.wp 7) (8 * L.wp) s₆.mem s₇.mem := o7'
  have en7 := en6.keep k7
  have y7 : arrP s₇.mem L 4 = y := by
    rw [arrP, o7.wordsVal (by omega) (by omega_arith), m6]; exact y5
  refine WP.seq (WP.mono (nonZero_ok en7 (a := 4) (c := 1) (by decide) v7
    ((k7.gpr (by decide)).trans b4)) fun s₈ ⟨⟨c4, m8⟩, k8⟩ => ?_)
  rw [show wordsVal s₇.mem L.S (slot L.wp 4) L.wp = y from y7, Bool.true_and] at c4
  have en8 := en7.keep k8
  -- y to the buffer.
  have k18 := ((((k13.trans k4).trans k5).trans k6).trans k7).trans k8
  have hm6 : s₆.mem = s₄.mem := by rw [m6, m5]
  have o47 : Outside L.S (slot L.wp 7) (8 * L.wp) s₃.mem s₇.mem := by
    rw [← hm6] at o4; exact o4.trans o7
  have b18 : Body L s.mem s₈.mem := by
    rw [m8]
    exact (Body.ofP hL o3 (yv_b1 L).1 (yv_b1 L).2).trans (Body.ofP hL o47 (yv_b7 L).1 (yv_b7 L).2.1)
  have hr8 : Regs s₈ L key x := hr.keep k18 b18
  refine WP.seq (WP.block_append (WP.mono (bufBase_ok (hs.congr k18.2.2) hL hr8 (rd := .s7) (t := .t2)
      (by decide) (by decide) (by decide)) fun u ⟨⟨f7, mu⟩, ku⟩ =>
    WP.mono (getP_ok (hs.congr (k18.trans ku).2.2) hL (hr8.keepM ku mu) .s8) fun s₉ ⟨⟨f8, m9⟩, k9⟩ => ?_))
  have hm9 : s₉.mem = s₇.mem := by rw [m9, mu, m8]
  have k19 := (k18.trans ku).trans k9
  refine WP.mono (storeBE_ok (j := 4) (O := L.Buf) (k := L.pl) (en8.keep (ku.trans k9)) (by decide)
    (by have := ScrL.bufSt (hs.congr k19.2.2) hL (o := 0) (k := L.pl) (by omega)
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.pl) (by omega) (by omega); simpa only [off, BitVec.add_zero] using this)
    ((k9.gpr (by decide)).trans f7) f8 (by omega) (by omega) (bufPastP hL)) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [hm9] at vt ot
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← hp0, ← hw8, show 8 * (8 * L.wp) = 64 * L.wp by omega]; exact wordsVal_lt _ _ _ _
  have kall := k19.trans kt
  refine ⟨⟨?_, (kt.gpr (by decide)).trans ((k9.gpr (by decide)).trans ((ku.gpr (by decide)).trans c4)),
    ⟨en8.keep ((ku.trans k9).trans kt), (kall.gpr (by decide)).trans hin.s6⟩,
    ((Body.ofP hL o3 (yv_b1 L).1 (yv_b1 L).2).trans (Body.ofP hL o47 (yv_b7 L).1 (yv_b7 L).2.1)).trans
      (Body.ofBuf hL ot (by omega)),
    ((PBody.of o3 (yv_b1 L).1 (yv_b1 L).2).keepQ hL |>.trans ((PBody.of o47 (yv_b7 L).1 (yv_b7 L).2.1).keepQ hL)).trans
      (bufKeepQ ot hpb)⟩, by simp only [List.append_assoc] at kall; exact kall⟩
  rw [vt, read_low _ _ (w := L.wp) (by rw [hw8]) (by
    show arrP s₇.mem L 4 < 2 ^ (8 * L.pl); rw [y7]; exact Nat.lt_trans hyp hplt)]
  exact y7

end VG.Proof.Dsa.RISCV64
