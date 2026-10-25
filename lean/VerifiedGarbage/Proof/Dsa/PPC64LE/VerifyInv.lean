module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr

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

/-- `rrQ`: `R² mod q` into arrays 1 and 8; array 9 is kept. -/
theorem rrQ_ok {s : State} {L : Lay} {key sig dig : Addr} (h : QS s L key sig dig)
    (hq : 2 ≤ arrQ s.mem L 0) :
    WP isa rrQ s fun t =>
      (QS t L key sig dig ∧ arrQ t.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0 ∧ QArr L s.mem t.mem ∧
        arrQ t.mem L 9 = arrQ s.mem L 9) ∧
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
    (QArr.of o4 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)).trans
      (QArr.of o5 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))
  have kt := (k13.trans k4).trans k5
  refine ⟨⟨h.step kt (by decide), ?_, qa, ?_⟩, kt.mono (by decide)⟩
  · generalize (2 : Nat) ^ (128 * 4) = R at v1 ⊢
    exact v8.trans v1
  · show val32 t.mem L.Q (slot 4 9) (2 * 4) = val32 s.mem L.Q (slot 4 9) (2 * 4)
    rw [Outside.val32 o5 (by simp only [slot_eq]; omega_arith) (by decide), Outside.val32 o4 (by simp only [slot_eq]; omega_arith)
      (by decide)]

/-- A subtraction `[t] := [a] − [m]` without a borrow, `[a] ≥ [m]`. -/
theorem sub_val {n A M T c : Nat} (hc : c ≤ 1) (hv : T + M = A + 2 ^ (32 * n) * c)
    (hT : T < 2 ^ (32 * n)) (hle : M ≤ A) : T = A - M := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> omega_arith

/-- The registers `qMinus2` writes. -/
def qm2Regs : List Reg := [.r0, .r3, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r20]

/-- `qMinus2`: the `q_len` octets of `q − 2` to the buffer, for `2 ≤ q < 2^(8 q_len)`. Arrays 0 and 8
are kept. -/
theorem qMinus2_ok {s : State} {L : Lay} {key sig dig : Addr} (h : QS s L key sig dig) (hL : L.Ok)
    (hq : 2 ≤ arrQ s.mem L 0) (hql : arrQ s.mem L 0 < 2 ^ (8 * L.ql)) :
    WP isa qMinus2 s fun t =>
      (QS t L key sig dig ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.ql) = arrQ s.mem L 0 - 2 ∧
        arrQ t.mem L 8 = arrQ s.mem L 8 ∧ QBuf L s.mem t.mem ∧ arrQ t.mem L 9 = arrQ s.mem L 9) ∧
        Keep qm2Regs s t := by
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
    Outside.val32 o1 (by rw [e70, e77]; omega_arith) (by decide)
  rw [v7, q1] at hv
  have v4 : val32 s₅.mem L.Q (slot 4 4) (2 * 4) = arrQ s.mem L 0 - 1 :=
    sub_val hc hv (val32_lt _ _ _ _) (by omega_arith)
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
    rw [Outside.val32 o5 (by rw [e74, e77]; omega_arith) (by decide)]; exact v7
  rw [v4, v7'] at hv'
  have v6 : val32 s₁₀.mem L.Q (slot 4 6) (2 * 4) = arrQ s.mem L 0 - 2 :=
    (sub_val hc' hv' (val32_lt _ _ _ _) (by omega_arith)).trans (by omega_arith)
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
      h.regs.keep (k110.trans k11)⟩
  refine WP.mono (ptrBuf_ok hL Q11.regs) fun s₁₂ ⟨⟨c12, c6, m12⟩, k12⟩ => ?_
  have e12 := e11.keep k12 (by decide)
  refine WP.mono (storeBE_ok (j := 6) (O := L.Buf) (k := L.ql) e12 (by decide)
    (ScrL.bufN (s := s₁₂) (Q11.scr.congr k12.wr) hL (by have := hL.pl; omega_arith)) c12 c6 (by omega_arith) (by omega_arith)
    (buf_sepQ L (by have := hL.pl; omega_arith))) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [m12, m11] at vt ot
  have kall := ((k110.trans k11).trans k12).trans kt
  have qb : QBuf L s.mem t.mem := qa10.qbuf.trans (QBuf.ofBuf hL ot (by have := hL.pl; omega_arith))
  have ot' : Outside (off L.Q 1600) 0 L.ql s₁₀.mem t.mem := by rw [← buf_eq]; exact ot
  have otq := outside_shift ot' (by have := hL.buf_end; have := hL.nowrap; have := hL.pl; omega_arith) (by decide)
  refine ⟨⟨⟨⟨e12.keep kt (by decide), (kall.gpr .r21 (by decide)).trans h.inq.h21,
      (kall.gpr .r23 (by decide)).trans h.inq.h23⟩, h.scr.congr kall.wr, h.regs.keep kall⟩,
    ?_, ?_, qb, ?_⟩, kall.mono (by decide)⟩
  · rw [vt, read_low (w := 4) _ _ (by omega_arith) (by rw [v6]; omega_arith), v6]
  · rw [arrQ, arr, Outside.val32 otq (by rw [e78]; omega_arith) (by decide),
      Outside.val32 o10 (by rw [e76, e78]; omega_arith) (by decide),
      Outside.val32 o5 (by rw [e74, e78]; omega_arith) (by decide),
      Outside.val32 o1 (by rw [e77, e78]; omega_arith) (by decide)]
  · have e79 : slot 4 9 = 688 := rfl
    rw [arrQ, arr, Outside.val32 otq (by rw [e79]; omega_arith) (by decide),
      Outside.val32 o10 (by rw [e76, e79]; omega_arith) (by decide),
      Outside.val32 o5 (by rw [e74, e79]; omega_arith) (by decide),
      Outside.val32 o1 (by rw [e77, e79]; omega_arith) (by decide)]

/-- An odd number's low word is odd. -/
theorem word_odd (m : Mem) (B : Addr) (d k : Nat) (hk : 1 ≤ k) (h : val32 m B d k % 2 = 1) :
    (word m B d).toNat % 2 = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  rw [val32] at h
  rw [word_eq_w32]
  omega_arith

/-- The buffer's bytes, kept by a change in the Q space's arrays. -/
theorem QArr.bufBytes {L : Lay} {m m' : Mem} (h : QArr L m m') {n : Nat} (hn : n ≤ 2 ^ 64 - 1600) :
    Spec.Rsa.bytesAt m' L.Buf n = Spec.Rsa.bytesAt m L.Buf n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  have hi := List.mem_range.mp hi
  have := buf_sepQ L (n := n) hn (L.Buf + BitVec.ofNat 64 i)
    (by rw [show L.Buf + BitVec.ofNat 64 i = off L.Buf i from rfl, ofs_off0 L.Buf (by omega_arith)]; exact hi)
  simp only [slot_eq]
  omega_arith

/-- The buffer's bytes are apart from the Q space. -/
theorem buf_apartQ (L : Lay) {n : Nat} (hn : n ≤ 2 ^ 64 - 1600) :
    ∀ i < n, ∀ x, ofs L.Q x < 1600 → off L.Buf i ≠ x := by
  intro i hi x hx e
  subst e
  have := buf_sepQ L hn (off L.Buf i) (by rw [ofs_off0 L.Buf (by omega_arith)]; exact hi)
  omega_arith

theorem pow_sq_eq (k : Nat) : (2 : Nat) ^ (64 * k) * 2 ^ (64 * k) = 2 ^ (128 * k) := by
  rw [← Nat.pow_add]; congr 1; omega_arith

/-- The registers `inverse` writes. -/
def invRegs : List Reg := [.r6, .r12] ++ loadRegs ++ copyRegs ++ [.r0, .r3, .r4, .r30, .r31] ++ ModExp.powSRegs

/-- `inverse`: s into array 4, then `s^e mod q` into array 4, for the `q_len`
octets `e` of the buffer. Array 8 is kept. -/
theorem inverse_ok {s : State} {L : Lay} {key sig dig : Addr} (h : QS s L key sig dig) (hL : L.Ok)
    (hsg : Src s L sig (2 * L.ql)) (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h8 : arrQ s.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0) :
    WP isa inverse s fun t =>
      (QS t L key sig dig ∧
        arrQ t.mem L 4 = sOf s.mem L sig ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) %
          arrQ s.mem L 0 ∧
        arrQ t.mem L 8 = arrQ s.mem L 8 ∧ QArr L s.mem t.mem) ∧ Keep invRegs s t := by
  have hRR := pow_sq_eq 4
  generalize (2 : Nat) ^ (128 * 4) = R2 at h8 hRR
  have hql := hL.ql
  have hpl := hL.pl
  have e70 : slot 4 0 = 256 := rfl
  have e71 : slot 4 1 = 304 := rfl
  have e74 : slot 4 4 = 448 := rfl
  have e78 : slot 4 8 = 640 := rfl
  unfold inverse
  refine WP.seq (WP.mono (ptrS_ok h.regs) fun s₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have Q1 := h.step k1 (by decide)
  refine WP.seq (WP.mono (loadQ_ok (j := 4) Q1 hL (by decide) (by decide)
      ((hsg.keep k1.rd k1.wr).sub (o := L.ql) (k := L.ql) (by omega_arith)) a12 a6 (by omega_arith) (by omega_arith))
    fun s₂ ⟨⟨Q2, v4, _, o2, qa2⟩, k2⟩ => ?_)
  rw [m1] at v4 o2 qa2
  refine WP.seq (WP.mono (copy_ok Q2.inq.env (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨v1, o3⟩, k3⟩ => ?_)
  have qa3 : QArr L s₂.mem s₃.mem := QArr.of o3 (by rw [e71]) (by rw [e71]; decide)
  have Q3 := Q2.step k3 (by decide)
  have a8s : arr s₂.mem L.Q 4 8 = arrQ s.mem L 8 := Outside.val32 o2 (by rw [e74, e78]; omega_arith) (by decide)
  have a0s : arr s₃.mem L.Q 4 0 = arrQ s.mem L 0 := (qa2.trans qa3).arr0
  have a4s : arr s₃.mem L.Q 4 4 = sOf s.mem L sig := by
    rw [arr, Outside.val32 o3 (by rw [e74, e71]; omega_arith) (by decide)]; exact v4
  have hbuf : Spec.Rsa.bytesAt s₃.mem L.Buf L.ql = Spec.Rsa.bytesAt s.mem L.Buf L.ql :=
    (qa2.trans qa3).bufBytes (by omega_arith)
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
    (by rw [hm6]; show arr s₃.mem L.Q 4 1 < arr s₃.mem L.Q 4 0; rw [a1s, a0s]; exact Nat.mod_lt _ (by omega_arith))
    (D := L.Buf) (L := L.ql)
    (show s₆.gpr .r30 = off L.Buf 0 by rw [k6.gpr .r30 (by decide), c30, off, BitVec.add_zero])
    ((k6.gpr .r31 (by decide)).trans c31)
    (by omega_arith) (by omega_arith)
    (fun i hi => by
      rw [k36.rd, k36.wr]
      exact (ScrL.bufN (s := s₃) Q3.scr hL (n := L.ql) (by omega_arith)).ld (show i + 1 ≤ L.ql by omega_arith))
    (buf_apartQ L (by omega_arith))) fun s₇ ⟨⟨pw, o7⟩, k7⟩ => ?_)
  rw [hm6] at pw o7
  have qa7 : QArr L s₃.mem s₇.mem := QArr.of (outs_within o7 (lo := slot 4 1) (hi := slot 4 8)
    (by simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false]; intro r hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot_eq] <;> omega_arith))
    (Nat.le_refl _) (by rw [e78, e71]; omega_arith)
  have o7' : Outside L.Q (slot 4 1) (slot 4 8 - slot 4 1) s₃.mem s₇.mem := outs_within o7
    (by simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false]; intro r hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot_eq] <;> omega_arith)
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
    by rw [mt]; exact qa2.trans (qa3.trans qa7)⟩, kall.mono (by decide)⟩
  · rw [arrQ, mt]
    have rr : val32 s₃.mem L.Q (slot 4 1) (2 * 4) = 2 ^ (64 * 4) * 2 ^ (64 * 4) % val32 s₃.mem L.Q (slot 4 0) (2 * 4) := by
      rw [hRR]; exact a1s.trans (by rw [← a0s])
    show val32 s₇.mem L.Q (slot 4 4) (2 * 4) = _
    rw [pw rr, hbuf]
    show arr s₃.mem L.Q 4 4 ^ _ % arr s₃.mem L.Q 4 0 = _
    rw [a4s, a0s]
  · rw [arrQ, mt]
    show val32 s₇.mem L.Q (slot 4 8) (2 * 4) = _
    rw [Outside.val32 o7' (by rw [e78, e71]; omega_arith) (by decide)]
    show arr s₃.mem L.Q 4 8 = _
    rw [arr, Outside.val32 o3 (by rw [e71, e78]; omega_arith) (by decide)]
    exact a8s

end VG.Proof.Dsa.PPC64LE
