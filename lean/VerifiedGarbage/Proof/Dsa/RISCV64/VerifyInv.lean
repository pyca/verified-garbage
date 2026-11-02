module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyQ
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: `R² mod q`, `q − 2` and `w = s^(q − 2) mod q`

In the Q space, q in array 0:

* `rrQ_ok`: `-q⁻¹ mod 2⁶⁴` into `t1`, `R² mod q` (`R = 2^(64 w)`) into arrays
  1 and 24;
* `minus2_ok`, `qMinus2_ok`: `q − 2` into array 6, then its `q_len` octets
  to the buffer;
* `inverse_ok`: s into array 4, and `s^(q − 2) mod q` into array 4.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
open VG.Proof.Bignum (slot)

/-- `-q⁻¹ mod 2⁶⁴` is in `t1`. -/
abbrev QInv (s : State) (L : Lay) : Prop :=
  ((word s.mem L.Q (slot L.wq 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0

/-- The registers `rrQ` writes. -/
def rrQRegs : List Reg := [.s0, .s1, .s2, .s3, .t1] ++ rrRegs

/-- `rrQ`: `-q⁻¹ mod 2⁶⁴` into `t1`, `R² mod q` into arrays 1 and 24. -/
theorem rrQ_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig)
    (hq : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) :
    WP isa rrQ s fun t =>
      (QS t L key sig ∧ QInv t L ∧ arrQ t.mem L 1 = 2 ^ (128 * L.wq) % arrQ s.mem L 0 ∧
        arrQ t.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0 ∧ QArr L s.mem t.mem) ∧ Keep rrQRegs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have e0 := Lay.slot_eq L.wq 0; have e1 := Lay.slot_eq L.wq 1; have e25 := Lay.slot_eq L.wq 25
  have e28 := Lay.slot_eq L.wq 28
  unfold rrQ
  have hodd : (word s.mem L.Q (slot L.wq 0)).toNat % 2 = 1 := by
    rw [wordsVal_mod_two _ _ _ (w := L.wq) (by omega)]; exact hqo
  refine WP.seq (WP.mono (minv_ok e.hs e.a7 (slot_al _ _) (by omega) hodd) fun s₁ ⟨⟨i1, m1⟩, k1⟩ => ?_)
  have e1' := e.keep k1
  refine WP.mono (rr_ok e1' (by rw [m1]; exact hq)) fun t ⟨⟨r1, r24, o⟩, kt⟩ => ?_
  rw [m1] at r1 r24 o
  have qa : QArr L s.mem t.mem := QArr.of o (by omega) (by omega)
  refine ⟨⟨h.step (k1.trans kt) (qa.body hL), ?_, r1, r24, qa⟩, k1.trans kt⟩
  show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [o.word (by omega) (by omega_arith), kt.gpr (by decide)]
  exact i1

/-- The registers `minus2` writes. -/
def m2Regs : List Reg := [.t3, .t4, .t5, .s4, .s2, .s0]

theorem sub_borrow (x : BitVec 64) {c : Nat} (hc : c ≤ 2) :
    (x - BitVec.ofNat 64 c).toNat + c = x.toNat + 2 ^ 64 * (if x.toNat < c then 1 else 0) := by
  have hx := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
  split <;> omega

theorem lt_ofNat (x : BitVec 64) {c : Nat} (hc : c ≤ 2) :
    (if x < BitVec.ofNat 64 c then (1 : BitVec 64) else 0) = BitVec.ofNat 64 (if x.toNat < c then 1 else 0) := by
  have : (x < BitVec.ofNat 64 c) ↔ x.toNat < c := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
  by_cases h : x.toNat < c <;> simp only [this, h, ite_true, ite_false] <;> rfl

/-- `minus2`: array 6 := `[0] − 2`, for `[0] ≥ 2`. -/
theorem minus2_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w)
    (hq : 2 ≤ wordsVal s.mem B (slot w 0) w) :
    WP isa minus2 s fun t =>
      (wordsVal t.mem B (slot w 6) w = wordsVal s.mem B (slot w 0) w - 2 ∧
        Outside B (slot w 6) (8 * w) s.mem t.mem) ∧ Keep m2Regs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ6 := h.arr (show 6 < 28 by decide)
  have hw2 := h.w2
  have hw48 := h.w48
  have e0 := Lay.slot_eq w 0; have e6 := Lay.slot_eq w 6
  have al0 := slot_al w 0
  have al6 := slot_al w 6
  unfold minus2
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .t3) (by decide) 0) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.keep k1).base (rd := .t4) (by decide) 6) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.t5, .s4] (Q := fun s₃ => s₃.gpr .t5 = BitVec.ofNat 64 w ∧
      s₃.gpr .s4 = BitVec.ofNat 64 2 ∧ s₃.mem = s₂.mem)
    (by brun [(k12.gpr (r := .t0) (by decide)).trans h.t0, BitVec.add_zero, exec_li_lit (show 2 < 2048 by decide)])
    (by rfl) (by rfl)) fun s₃ ⟨⟨b5, b4, m3⟩, k3⟩ => ?_
  have k123 := k12.trans k3
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w 0 + 8 * i) ∧ t.gpr .t4 = off B (slot w 6 + 8 * i) ∧
      (∃ c, c ≤ 2 ∧ t.gpr .s4 = BitVec.ofNat 64 c ∧
        wordsVal t.mem B (slot w 6) i + 2 = wordsVal s.mem B (slot w 0) i + 2 ^ (64 * i) * c) ∧
      Outside B (slot w 6) (8 * i) s.mem t.mem ∧ Keep m2Regs s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s2 .t3 0, .sltu .s0 .s2 .s4, .sub .s2 .s2 .s4,
      .addi .s4 .s0 0, .store .d .s2 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith) (by omega)
    Inv (fun i hi t ⟨j3, j4, ⟨c, hc, jc, jv⟩, jout, jk⟩ hcnt => ?_)
    ⟨by rw [k3.gpr (by decide), k2.gpr (by decide), a3]; rfl, by rw [k3.gpr (by decide), a4]; rfl,
      ⟨2, by decide, b4, by simp [wordsVal]⟩, by rw [m3, m2, m1]; exact Outside.refl _ _ _ _,
      k123.mono (by decide)⟩ b5)
    fun t ⟨_, _, ⟨c, hc, _, tv⟩, tout, tk⟩ => ⟨⟨?_, tout⟩, tk⟩
  · have hx : word t.mem B (slot w 0 + 8 * i) = word s.mem B (slot w 0 + 8 * i) :=
      jout.word (by omega) (by omega_arith)
    have hst : WP isa (.block [.load .d .s2 .t3 0, .sltu .s0 .s2 .s4, .sub .s2 .s2 .s4,
        .addi .s4 .s0 0, .store .d .s2 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .t5 .t5 (-1)]) t
        fun t' => t' = (((({ ((((t.write .s2 (word t.mem B (slot w 0 + 8 * i))).write .s0
          (if word t.mem B (slot w 0 + 8 * i) < BitVec.ofNat 64 c then 1 else 0)).write .s2
          (word t.mem B (slot w 0 + 8 * i) - BitVec.ofNat 64 c)).write .s4
          (if word t.mem B (slot w 0 + 8 * i) < BitVec.ofNat 64 c then 1 else 0)) with
          mem := t.mem.writeW (off B (slot w 6 + 8 * i)) (word t.mem B (slot w 0 + 8 * i) - BitVec.ofNat 64 c) } :
            State).write .t3 (off B (slot w 0 + 8 * i + 8))).write .t4 (off B (slot w 6 + 8 * i + 8))).write .t5
              (t.gpr .t5 - BitVec.ofNat 64 1)) := by
      brun [j3, j4, jc, BitVec.add_zero, (hs.congr jk.2.2).ld (show slot w 0 + 8 * i + 8 ≤ Z by omega_arith),
        (hs.congr jk.2.2).al8 (show slot w 0 + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
        (hs.congr jk.2.2).st (show slot w 6 + 8 * i + 8 ≤ Z by omega_arith),
        (hs.congr jk.2.2).al8 (show slot w 6 + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw := writeW_outside t.mem B (d := slot w 6 + 8 * i)
      (word t.mem B (slot w 0 + 8 * i) - BitVec.ofNat 64 c) (by omega_arith)
    refine ⟨⟨by gsimp; rw [show slot w 0 + 8 * i + 8 = slot w 0 + 8 * (i + 1) by omega],
      by gsimp; rw [show slot w 6 + 8 * i + 8 = slot w 6 + 8 * (i + 1) by omega], ?_, ?_, ?_⟩, by gsimp⟩
    · refine ⟨if (word s.mem B (slot w 0 + 8 * i)).toNat < c then 1 else 0, by split <;> omega, ?_, ?_⟩
      · gsimp; rw [lt_ofNat _ hc, hx]
      · gsimp
        rw [wordsVal_succ_top, wordsVal_succ_top, word_writeW_self,
          hw.wordsVal (Or.inl (Nat.le_refl _)) (by omega_arith), hx]
        have hb := sub_borrow (word s.mem B (slot w 0 + 8 * i)) hc
        have key := congrArg (fun z => 2 ^ (64 * i) * z) hb
        simp only [Nat.mul_add] at key
        rw [show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add, Nat.mul_assoc]
        omega
    · gsimp; exact (jout.mono (Nat.le_refl _) (by omega)).trans (hw.mono (by omega) (by omega))
    · exact Keep.trans' jk (((((((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))
  · have hlt := wordsVal_lt t.mem B (slot w 6) w
    have hlt0 := wordsVal_lt s.mem B (slot w 0) w
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl <;> omega

theorem slot_mono {w j k : Nat} (h : j ≤ k) : slot w j ≤ slot w k := by
  rw [Lay.slot_eq, Lay.slot_eq]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem m2_sep {L : Lay} (hL : L.Ok) : ∀ x, ofs L.Buf x < L.ql → 1600 ≤ ofs L.Q x :=
  buf_sepQ L (by rcases hL.ql with e | e | e <;> omega)

/-- The registers `qMinus2` writes. -/
def qm2Regs : List Reg := m2Regs ++ [.s7, .t2, .s8] ++ storeRegs

/-- `qMinus2`: the `q_len` octets of `q − 2` to the buffer, for
`2 ≤ q < 2^(8 q_len)`. Arrays 0–5 and 7–27 are kept. -/
theorem qMinus2_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig)
    (hq : 2 ≤ arrQ s.mem L 0) (hql : arrQ s.mem L 0 < 2 ^ (8 * L.ql)) :
    WP isa qMinus2 s fun t =>
      (QS t L key sig ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.ql) = arrQ s.mem L 0 - 2 ∧
        (∀ j < 28, j ≠ 6 → arrQ t.mem L j = arrQ s.mem L j) ∧
        word t.mem L.Q (slot L.wq 0) = word s.mem L.Q (slot L.wq 0) ∧ QBuf L s.mem t.mem) ∧
        Keep qm2Regs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega
  have hql' : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have e1 := Lay.slot_eq L.wq 1; have e6 := Lay.slot_eq L.wq 6; have e7 := Lay.slot_eq L.wq 7; have e28 := Lay.slot_eq L.wq 28
  unfold qMinus2
  refine WP.seq (WP.mono (minus2_ok e hq) fun s₁ ⟨⟨v6, o1⟩, k1⟩ => ?_)
  have Q1 := h.step k1 (Body.ofQ hL o1 (by omega))
  refine WP.seq (WP.mono (ptrBuf_ok Q1.scr hL Q1.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_)
  have e2 := Q1.inq.env.keep k2
  refine WP.mono (storeBE_ok (j := 6) (O := L.Buf) (k := L.ql) e2 (by decide)
    (by have := ScrL.bufSt (Q1.scr.congr k2.2.2) hL (o := 0) (k := L.ql) (by omega)
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.ql) (by omega) (by omega); simpa only [off, BitVec.add_zero] using this) a7 a8 (by omega) (by omega) (m2_sep hL))
    fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [m2] at vt ot
  have qb : QBuf L s₁.mem t.mem := QBuf.ofBuf hL ot (by omega)
  have ot' : Outside (off L.Q 1600) 0 L.ql s₁.mem t.mem := by rw [← buf_eq]; exact ot
  have otq := outside_shift ot' (by have := hL.buf_end; have := hL.nowrap; simp only [Lay.bOff] at *; omega)
    (by decide)
  have k := (k1.trans k2).trans kt
  refine ⟨⟨Q1.step (k2.trans kt) (qb.body hL), ?_, fun j hj hj6 => ?_, ?_,
    (QArr.of o1 (by omega) (by omega)).qbuf hL |>.trans qb⟩, k.mono (by decide)⟩
  · have hql2 : wordsVal s.mem L.Q (slot L.wq 0) L.wq < 2 ^ (8 * L.ql) := hql
    have hq2 : 2 ≤ wordsVal s.mem L.Q (slot L.wq 0) L.wq := hq
    rw [vt, read_low _ _ (w := L.wq) (by omega) (by rw [v6]; omega), v6]
  · have := slot_lt (w := L.wq) hj
    have sj := VG.Proof.Bignum.slot_sep (w := L.wq) hj6
    rw [arrQ, otq.wordsVal (Or.inl (by omega)) (by omega_arith), o1.wordsVal (by omega) (by omega_arith)]
  · have e0 := Lay.slot_eq L.wq 0
    rw [otq.word (Or.inl (by omega)) (by omega_arith), o1.word (by omega) (by omega_arith)]

/-- The registers `inverse` writes. -/
def invRegs : List Reg := [.s7, .s8] ++ loadRegs ++ copyRegs ++ [.s7, .t2, .s8, .s9, .s10] ++ Win.powWRegs

/-- `inverse`: s into array 4, then `s^e mod q` into array 4, for the `q_len`
octets `e` of the buffer. Arrays 24–27 and `t1` are kept. -/
theorem inverse_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig) (hi : QInv s L)
    (hsg : Src s L sig (2 * L.ql)) (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h24 : arrQ s.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0) :
    WP isa inverse s fun t =>
      (QS t L key sig ∧ QInv t L ∧
        arrQ t.mem L 4 = sOf s.mem L sig ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) %
          arrQ s.mem L 0 ∧
        (∀ j < 28, 24 ≤ j → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧ Keep invRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e28 := e 28
  unfold inverse
  refine WP.seq (WP.mono (ptrS_ok h.scr hL h.regs) fun s₁ ⟨⟨a7, a8, m1⟩, k1⟩ => ?_)
  have Q1 := h.stepM k1 m1
  refine WP.seq (WP.mono (loadQ_ok (j := 4) Q1 hL (by decide)
      ((hsg.keep k1.2.1 k1.2.2).sub (o := L.ql) (k := L.ql) (by omega)) a7 a8 (by omega) (by omega))
    fun s₂ ⟨⟨Q2, v4, _, o2⟩, k2⟩ => ?_)
  rw [m1] at v4 o2
  refine WP.seq (WP.mono (copy_ok Q2.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨c1, o3⟩, k3⟩ => ?_)
  have Q3 := Q2.step k3 (Body.ofQ hL o3 (by omega))
  have A0 : arrQ s₃.mem L 0 = arrQ s.mem L 0 := by
    rw [arrQ, o3.wordsVal (by omega) (by omega_arith), o2.wordsVal (by omega) (by omega_arith)]
  have W0 : word s₃.mem L.Q (slot L.wq 0) = word s.mem L.Q (slot L.wq 0) := by
    rw [o3.word (by omega) (by omega_arith), o2.word (by omega) (by omega_arith)]
  have A4 : arrQ s₃.mem L 4 = sOf s.mem L sig := by
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
