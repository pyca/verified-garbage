module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA verification on PPC64LE: `R² mod q`, `q − 2` and `w = s^(q − 2) mod q`

In the Q space, q in array 0:

* `rrQ_ok`: `R² mod q` (`R = 2^256`) into arrays 1 and 8;
* `qMinus2_ok`: `q − 2`'s `q_len` octets to the buffer;
* `inverse_ok`: s into array 4, and `s^(q − 2) mod q` into array 4.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

/-- The registers `rrQ` writes. -/
def rrRegs : List Reg := [.r5, .r8, .r9, .r0, .r3, .r4, .r14, .r15, .r16, .r17, .r20] ++ copyRegs

/-- `rrQ`: `R² mod q` into arrays 1 and 8. -/
theorem rrQ_ok {s : State} {L : Lay} {key sig dig : Addr} (h : QS s L key sig dig) (hL : L.Ok)
    (hq : 2 ≤ arrQ s.mem L 0) :
    WP isa rrQ s fun t =>
      (QS t L key sig dig ∧ arrQ t.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0 ∧ QArr L s.mem t.mem) ∧
        Keep rrRegs s t := by
  have e := h.inq.env
  unfold rrQ
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e.base (rd := .r5) (by decide) (by decide) 1) fun s₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  have e1 := e.keep k1 (by decide)
  refine WP.mono (e1.base (rd := .r8) (by decide) (by decide) 2) fun s₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have e2 := e1.keep k2 (by decide)
  refine WP.mono (e2.base (rd := .r9) (by decide) (by decide) 3) fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have e3 := e2.keep k3 (by decide)
  have hm3 : s₃.mem = s.mem := by rw [m3, m2, m1]
  have k13 := (k1.trans k2).trans k3
  refine WP.seq (WP.mono (r2_ok e3.hs ((k3.gpr .r8 (by decide)).trans a8) a9 e3.h10
    ((k3.gpr .r5 (by decide)).trans ((k2.gpr .r5 (by decide)).trans a5)) e3.h11 (by decide) (by decide)
    (by decide) (by rw [hm3]; exact hq)) fun s₄ ⟨v1, o4, k4⟩ => ?_)
  rw [hm3] at v1 o4
  have e4 := e3.keep k4 (by decide)
  refine WP.mono (copy_ok e4 (o := 8) (a := 1) (by decide) (by decide) (by decide)) fun t ⟨⟨v8, o5⟩, k5⟩ => ?_
  have qa : QArr L s.mem t.mem :=
    (QArr.of o4 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)).trans
      (QArr.of o5 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega))
  have kt := (k13.trans k4).trans k5
  refine ⟨⟨h.step hL kt (by decide) qa, ?_, qa⟩, kt.mono (by decide)⟩
  generalize (2 : Nat) ^ (128 * 4) = R at v1 ⊢
  exact v8.trans v1

/-- A subtraction `[t] := [a] − [m]` without a borrow, `[a] ≥ [m]`. -/
theorem sub_val {n A M T c : Nat} (hc : c ≤ 1) (hv : T + M = A + 2 ^ (32 * n) * c)
    (hT : T < 2 ^ (32 * n)) (hle : M ≤ A) : T = A - M := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> omega

/-- The registers `qMinus2` writes. -/
def qm2Regs : List Reg := [.r0, .r3, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r20]

/-- `qMinus2`: the `q_len` octets of `q − 2` to the buffer, for `2 ≤ q < 2^(8 q_len)`. Arrays 0 and 8
are kept. -/
theorem qMinus2_ok {s : State} {L : Lay} {key sig dig : Addr} (h : QS s L key sig dig) (hL : L.Ok)
    (hq : 2 ≤ arrQ s.mem L 0) (hql : arrQ s.mem L 0 < 2 ^ (8 * L.ql)) :
    WP isa qMinus2 s fun t =>
      (QS t L key sig dig ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.ql) = arrQ s.mem L 0 - 2 ∧
        arrQ t.mem L 8 = arrQ s.mem L 8 ∧ QBuf L s.mem t.mem) ∧ Keep qm2Regs s t := by
  have e := h.inq.env
  have hn : slot 4 28 ≤ 2 ^ 64 := by decide
  have hq' := hL.ql
  unfold qMinus2
  refine WP.seq (WP.mono (Pub.oneP_ok e.hs (by decide) (by decide) (by decide) e.h10 e.h29 e.h11)
    fun s₁ ⟨⟨v7, o1⟩, k1⟩ => ?_)
  have e1 := e.keep k1 (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e1.base (rd := .r8) (by decide) (by decide) 0) fun s₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have e2 := e1.keep k2 (by decide)
  refine WP.mono (e2.base (rd := .r9) (by decide) (by decide) 4) fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have e3 := e2.keep k3 (by decide)
  refine WP.mono (e3.base (rd := .r10) (by decide) (by decide) 7) fun s₄ ⟨⟨a10, m4⟩, k4⟩ => ?_
  have k24 := (k2.trans k3).trans k4
  have hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  have k14 := k1.trans k24
  have hs4 : Scr s₄ L.Q 1600 := e.hs.congr k14.wr
  have e70 : slot 4 0 = 256 := rfl
  have e74 : slot 4 4 = 448 := rfl
  have e76 : slot 4 6 = 544 := rfl
  have e77 : slot 4 7 = 592 := rfl
  have e78 : slot 4 8 = 640 := rfl
  -- `[4] := q − 1`.
  refine WP.seq (WP.mono (subMod_ok (dA := slot 4 0) (dT := slot 4 4) (dM := slot 4 7) (n := 2 * 4) hs4
    ((k4.gpr .r8 (by decide)).trans ((k3.gpr .r8 (by decide)).trans a8)) ((k4.gpr .r9 (by decide)).trans a9)
    a10 ((k14.gpr .r11 (by decide)).trans e.h11) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨⟨c, hc, hv, _⟩, o5, k5⟩ => ?_)
  rw [hm4] at hv o5
  have q1 : val32 s₁.mem L.Q (slot 4 0) (2 * 4) = arrQ s.mem L 0 :=
    Outside.val32 o1 (by rw [e70, e77]; omega) (by decide)
  rw [v7, q1] at hv
  have v4 : val32 s₅.mem L.Q (slot 4 4) (2 * 4) = arrQ s.mem L 0 - 1 :=
    sub_val hc hv (val32_lt _ _ _ _) (by omega)
  -- `[6] := [4] − 1`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  have k15 := k14.trans k5
  refine WP.mono (WP.keep [.r10] (Q := fun u => u.gpr .r10 = off L.Q (slot 4 0) ∧ u.mem = s₅.mem) (by
      prun [(k15.gpr .r31 (by decide)).trans e.h31, hdrBytes]
      rfl) (by decide)) fun s₆ ⟨⟨a10', m6⟩, k6⟩ => ?_
  have e6 : Env s₆ L.Q 1600 4 := env_keep10 e (k15.trans k6) (by decide) a10'
  refine WP.mono (e6.base (rd := .r8) (by decide) (by decide) 4) fun s₇ ⟨⟨b8, m7⟩, k7⟩ => ?_
  have e7 := e6.keep k7 (by decide)
  refine WP.mono (e7.base (rd := .r9) (by decide) (by decide) 6) fun s₈ ⟨⟨b9, m8⟩, k8⟩ => ?_
  have e8 := e7.keep k8 (by decide)
  refine WP.mono (e8.base (rd := .r10) (by decide) (by decide) 7) fun s₉ ⟨⟨b10, m9⟩, k9⟩ => ?_
  have hm9 : s₉.mem = s₅.mem := by rw [m9, m8, m7, m6]
  have k69 := (k6.trans k7).trans k8 |>.trans k9
  refine WP.seq (WP.mono (subMod_ok (dA := slot 4 4) (dT := slot 4 6) (dM := slot 4 7) (n := 2 * 4)
    (e6.hs.congr ((k7.trans k8).trans k9).wr) ((k9.gpr .r8 (by decide)).trans ((k8.gpr .r8 (by decide)).trans b8))
    ((k9.gpr .r9 (by decide)).trans b9) b10 ((k69.gpr .r11 (by decide)).trans ((k15.gpr .r11
      (by decide)).trans e.h11)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁₀ ⟨⟨c', hc', hv', _⟩, o10, k10⟩ => ?_)
  rw [hm9] at hv' o10
  have v7' : val32 s₅.mem L.Q (slot 4 7) (2 * 4) = 1 := by
    rw [Outside.val32 o5 (by rw [e74, e77]; omega) (by decide)]; exact v7
  rw [v4, v7'] at hv'
  have v6 : val32 s₁₀.mem L.Q (slot 4 6) (2 * 4) = arrQ s.mem L 0 - 2 :=
    (sub_val hc' hv' (val32_lt _ _ _ _) (by omega)).trans (by omega)
  -- To the buffer.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have k110 := ((k15.trans k69).trans k10)
  refine WP.mono (WP.keep [.r10] (Q := fun u => u.gpr .r10 = off L.Q (slot 4 0) ∧ u.mem = s₁₀.mem) (by
      prun [(k110.gpr .r31 (by decide)).trans e.h31, hdrBytes]
      rfl) (by decide)) fun s₁₁ ⟨⟨a10'', m11⟩, k11⟩ => ?_
  have e11 : Env s₁₁ L.Q 1600 4 := env_keep10 e (k110.trans k11) (by decide) a10''
  have qa10 : QArr L s.mem s₁₀.mem :=
    ((QArr.of o1 (by rw [e77]; decide) (by rw [e77]; decide)).trans
      (QArr.of o5 (by rw [e74]; decide) (by rw [e74]; decide))).trans
      (QArr.of o10 (by rw [e76]; decide) (by rw [e76]; decide))
  have Q11 : QS s₁₁ L key sig dig :=
    ⟨⟨e11, (k110.trans k11 |>.gpr .r21 (by decide)).trans h.inq.h21,
      (k110.trans k11 |>.gpr .r23 (by decide)).trans h.inq.h23⟩, h.scr.congr (k110.trans k11).wr,
      h.hdr.body (by rw [m11]; exact qa10.qbody.body hL) hL⟩
  refine WP.mono (ptrBuf_ok hL Q11.scr Q11.hdr Q11.inq.h21) fun s₁₂ ⟨⟨c12, c6, m12⟩, k12⟩ => ?_
  have e12 := e11.keep k12 (by decide)
  refine WP.mono (storeBE_ok (j := 6) (O := L.Buf) (k := L.ql) e12 (by decide)
    (ScrL.bufN (s := s₁₂) (Q11.scr.congr k12.wr) hL (by have := hL.pl; omega)) c12 c6 (by omega) (by omega)
    (buf_sepQ L (by have := hL.pl; omega))) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [m12, m11] at vt ot
  have kall := ((k110.trans k11).trans k12).trans kt
  have qb : QBuf L s.mem t.mem := qa10.qbuf.trans (QBuf.ofBuf hL ot (by have := hL.pl; omega))
  refine ⟨⟨⟨⟨e12.keep kt (by decide), (kall.gpr .r21 (by decide)).trans h.inq.h21,
      (kall.gpr .r23 (by decide)).trans h.inq.h23⟩, h.scr.congr kall.wr, h.hdr.body (qb.body hL) hL⟩,
    ?_, ?_, qb⟩, kall.mono (by decide)⟩
  · rw [vt, read_low (w := 4) _ _ (by omega) (by rw [v6]; omega), v6]
  · have ot' : Outside (off L.Q 1600) 0 L.ql s₁₀.mem t.mem := by rw [← buf_eq]; exact ot
    have otq := outside_shift ot' (by have := hL.buf_end; have := hL.nowrap; have := hL.pl; omega) (by decide)
    rw [arrQ, arr, Outside.val32 otq (by rw [e78]; omega) (by decide),
      Outside.val32 o10 (by rw [e76, e78]; omega) (by decide),
      Outside.val32 o5 (by rw [e74, e78]; omega) (by decide),
      Outside.val32 o1 (by rw [e77, e78]; omega) (by decide)]

end VG.Proof.Dsa.PPC64LE
