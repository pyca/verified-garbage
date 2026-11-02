module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
public import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on RISC-V: q, p and the domain's elements

As on PPC64LE (`Proof/Dsa/PPC64LE/Elem.lean`):

* `setupQ_ok`, `pModQ_ok`: q into the Q space's array 0, and `a0 = 0`
  exactly when `p mod q = 1`;
* `setupP_ok`: p into the P space's array 0, `-p⁻¹ mod 2⁶⁴` into `t1`, and
  `R² mod p` into its arrays 1 and 24.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- Array `j` of the P space. -/
abbrev arrP (m : Mem) (L : Lay) (j : Nat) : Nat := wordsVal m L.S (slot L.wp j) L.wp

/-- Array `j` of the Q space. -/
abbrev arrQ (m : Mem) (L : Lay) (j : Nat) : Nat := wordsVal m L.Q (slot L.wq j) L.wq

theorem unmask_eq (b : Bool) :
    (mask b &&& BitVec.ofInt 64 1) ^^^ BitVec.ofInt 64 1 = BitVec.ofNat 64 (if b then 0 else 1) := by
  cases b <;> rfl

/-- `unmask`: `a0 = 0` exactly when the mask of `b` in `a0` is all ones. -/
theorem unmask_ok (s : State) {b : Bool} (h0 : s.gpr .a0 = mask b) :
    WP isa (.block unmask) s fun t => ((t.gpr .a0 = 0 ↔ b = true) ∧ t.mem = s.mem) ∧ Keep [.a0] s t := by
  refine WP.keep _ ?_ (by decide) (by rfl)
  unfold unmask
  brun [h0]
  cases b <;> decide

/-- A number of words has the parity of its first word. -/
theorem wordsVal_mod_two (m : Mem) (B : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    (word m B d).toNat % 2 = wordsVal m B d w % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [wordsVal]
  omega

/-- The registers `setupQ` writes. -/
def setupQRegs : List Reg := enterRegs ++ ptrRegs ++ loadRegs

/-- `setupQ`: into the Q space, and q into its array 0 (word `w` zero). -/
theorem setupQ_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hk : Src s L key (2 * L.pl + L.ql)) :
    WP isa setupQ s fun t =>
      (InQ t L ∧ arrQ t.mem L 0 = qOf s.mem L key ∧ word t.mem L.Q (slot L.wq 0 + 8 * L.wq) = 0 ∧
        QBody L s.mem t.mem) ∧ Keep setupQRegs s t := by
  have hbuf := hL.buf_end
  have hnw := hL.nowrap
  have hq0 := hL.qOff_eq
  have hwq := hL.wq_ge
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hsepK : ∀ i < 2 * L.pl + L.ql, ∀ x, ofs L.Q x < 1600 → off key i ≠ x :=
    hk.sepIn (a := L.qOff) (by simp only [Lay.bOff] at hbuf; omega_arith) hnw
  unfold setupQ
  refine WP.seq (WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (ptrQ_ok (hs.congr k1.2.2) hL (hr.keepM k1 m1)) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have hkq := (hk.sub (o := L.pl) (k := L.ql) (by omega_arith)).keep k12.2.1 k12.2.2
  have e2 : Env s₂ L.Q 1600 L.wq := q1.env.keep k2
  refine WP.mono (loadArr_ok e2 (j := 0) (N := off key L.pl) (by decide) (by rw [a7]; exact (BitVec.add_zero _).symm)
    a8 (by omega) hwq.2.2 hkq.rd (fun i hi => by rw [off_off]; exact hsepK _ (by omega_arith)))
    fun s₃ ⟨⟨v0, top0, o3, a10⟩, k3⟩ => ?_
  rw [m2, m1] at v0 o3
  refine ⟨⟨⟨⟨e2.hs.congr k3.2.2, a10, (k3.gpr (by decide)).trans e2.s5, (k3.gpr (by decide)).trans e2.t0,
    e2.w2, e2.w48, e2.hZ⟩, ((k2.trans k3).gpr (by decide)).trans q1.s6⟩, v0, top0,
    o3.mono (by simp only [Lay.slot_eq]; omega) (by have := hL.qslot; simp only [Lay.slot_eq] at this ⊢; omega)⟩,
    (k12.trans k3).mono (by decide)⟩

/-- The registers `pModQ` writes. -/
def pModQRegs : List Reg :=
  setupQRegs ++ ModArith.redRegs ++ ([.a0, .a2, .a5, .a6, .s0, .s1, .s9, .s10, .t2, .t3, .t4, .t5] : List Reg)

/-- `pModQ`: into the Q space, q into its array 0 (word `w` zero), and `a0 = 0`
exactly when `p mod q = 1`. -/
theorem pModQ_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hk : Src s L key (2 * L.pl + L.ql)) (hq : 0 < qOf s.mem L key) :
    WP isa pModQ s fun t =>
      (InQ t L ∧ arrQ t.mem L 0 = qOf s.mem L key ∧ word t.mem L.Q (slot L.wq 0 + 8 * L.wq) = 0 ∧
        (t.gpr .a0 = 0 ↔ pOf s.mem L key % qOf s.mem L key = 1) ∧ QBody L s.mem t.mem) ∧
        Keep pModQRegs s t := by
  have hZ := hL.z256
  have hbuf := hL.buf_end
  have hnw := hL.nowrap
  have hq0 := hL.qOff_eq
  have hwq := hL.wq_ge
  have hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega_arith
  have hsepK : ∀ i < 2 * L.pl + L.ql, ∀ x, ofs L.Q x < 1600 → off key i ≠ x :=
    hk.sepIn (a := L.qOff) (by simp only [Lay.bOff] at hbuf; omega_arith) hnw
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e7 := e 7; have e8 := e 8; have e28 := e 28
  have hqs := hL.qslot
  unfold pModQ
  refine WP.seq (WP.mono (setupQ_ok hL hs hr hk) fun s₃ ⟨⟨q3, v0, top0, qb3⟩, k13⟩ => ?_)
  have e3 : Env s₃ L.Q 1600 L.wq := q3.env
  have hr₃ : Regs s₃ L key sig := hr.keep k13 (qb3.body hL)
  have hs₃ : ScrL s₃ L := hs.congr k13.2.2
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = off key 0 ∧ u.mem = s₃.mem)
    (by brun [hr₃.s11, BitVec.add_zero]) (by rfl) (by rfl)) fun s₄ ⟨⟨a9, m4⟩, k4⟩ =>
    WP.mono (getP_ok (hs₃.congr k4.2.2) hL (hr₃.keepM k4 m4) .s10) fun s₅ ⟨⟨a10, m5⟩, k5⟩ => ?_))
  have k35 := k4.trans k5
  have e5 : Env s₅ L.Q 1600 L.wq := e3.keep k35
  have m35 : s₅.mem = s₃.mem := by rw [m5, m4]
  have v0' : wordsVal s₃.mem L.Q (slot L.wq 0) L.wq = qOf s.mem L key := v0
  have hkb : Spec.Rsa.bytesAt s₃.mem key L.pl = Spec.Rsa.bytesAt s.mem key L.pl :=
    (hk.take (k := L.pl) (by omega)).bytes (qb3.body hL) (by omega)
  refine WP.seq (WP.mono (ModArith.reduce64_ok (D := key) (L := L.pl) e5.hs (by omega) (by omega)
    (by omega) e5.a7 e5.s5 e5.t0 (by rw [m35, v0']; exact hq) ((k5.gpr (by decide)).trans a9) a10 (by omega)
    (by omega_arith) (fun i hi => by rw [(k13.trans k35).2.1, (k13.trans k35).2.2]; exact hk.rd i (by omega_arith))
    (fun i hi => hsepK i (by omega_arith))) fun s₆ ⟨⟨r1, o6⟩, k6⟩ => ?_)
  rw [m35, hkb, v0'] at r1
  rw [m35] at o6
  have e6 := e5.keep k6
  refine WP.seq (WP.mono (Pub.oneP_ok e6.hs (by omega) (by omega) (by omega) e6.a7 e6.s5 e6.t0)
    fun s₇ ⟨⟨v7, o7'⟩, k7⟩ => ?_)
  have o7 : Outside L.Q (slot L.wq 7) (8 * L.wq) s₆.mem s₇.mem := o7'
  have e7 := e6.keep k7
  refine WP.seq (WP.mono (eqMask_ok e7 (j := 1) (k := 7) (rd := .a0) (by decide) (by decide) (by decide))
    fun s₈ ⟨⟨a0, m8⟩, k8⟩ => ?_)
  refine WP.mono (unmask_ok s₈ a0) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have hmt : t.mem = s₇.mem := by rw [mt, m8]
  have o3t : Outside L.Q (slot L.wq 1) (8 * (8 * (L.wq + 2))) s₃.mem t.mem := by
    rw [hmt]; exact (o6.mono (by omega) (by omega)).trans (o7.mono (by omega) (by omega))
  have p1 : arrQ s₇.mem L 1 = pOf s.mem L key % qOf s.mem L key := by
    rw [arrQ, o7.wordsVal (by omega) (by omega_arith), r1]; rfl
  have k8t := ((k6.trans k7).trans k8).trans kt
  refine ⟨⟨⟨e6.keep ((k7.trans k8).trans kt), ((k35.trans k8t).gpr (by decide)).trans q3.s6⟩, ?_, ?_, ?_, ?_⟩,
    ((k13.trans k35).trans k8t).mono (by decide)⟩
  · rw [arrQ, o3t.wordsVal (by omega) (by omega_arith)]; exact v0
  · rw [o3t.word (by omega) (by omega_arith)]; exact top0
  · rw [t0, decide_eq_true_iff, ← p1]
    rw [show wordsVal s₇.mem L.Q (slot L.wq 7) L.wq = 1 from v7]
  · exact qb3.trans (o3t.mono (by omega) (by omega))

theorem pbody_of_arrays {L : Lay} {m m₁ m₂ : Mem} (o3 : Outside L.S (slot L.wp 0) (8 * (L.wp + 1)) m m₁)
    (o5 : Outside L.S (slot L.wp 1) (24 * (8 * (L.wp + 2))) m₁ m₂) : PBody L m m₂ :=
  (o3.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.qOff, Lay.slot_eq]; omega)).trans
    (o5.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.qOff, Lay.slot_eq]; omega))

/-- The registers `setupP` writes. -/
def setupPRegs : List Reg :=
  enterRegs ++ ptrRegs ++ loadRegs ++ ([.s1, .s2, .s3, .t1] : List Reg) ++ rrRegs

/-- `setupP`: into the P space, p into its array 0 (word `w` zero),
`-p⁻¹ mod 2⁶⁴` into `t1` and `R² mod p` (`R = 2^(64 w)`) into its arrays 1
and 24. -/
theorem setupP_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hk : Src s L key (2 * L.pl + L.ql))
    (hp : 2 ≤ pOf s.mem L key) (hpo : pOf s.mem L key % 2 = 1) :
    WP isa setupP s fun t =>
      (InP t L ∧ arrP t.mem L 0 = pOf s.mem L key ∧ word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        ((word t.mem L.S (slot L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧
        arrP t.mem L 1 = 2 ^ (128 * L.wp) % pOf s.mem L key ∧
        arrP t.mem L 24 = 2 ^ (128 * L.wp) % pOf s.mem L key ∧ PBody L s.mem t.mem) ∧
        Keep setupPRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hbuf := hL.buf_end
  have hq0 := hL.qOff_eq
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e24 := e 24; have e25 := e 25; have e28 := e 28
  have hsepK : ∀ i < 2 * L.pl + L.ql, ∀ x, ofs L.S x < L.qOff → off key i ≠ x := fun i hi x hx =>
    hk.sep i hi x (by simp only [Lay.bOff] at hbuf; omega_arith)
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hbuf := hL.buf_end
  have hq0 := hL.qOff_eq
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e24 := e 24; have e25 := e 25; have e28 := e 28
  have hsepK : ∀ i < 2 * L.pl + L.ql, ∀ x, ofs L.S x < L.qOff → off key i ≠ x := fun i hi x hx =>
    hk.sep i hi x (by simp only [Lay.bOff] at hbuf; omega_arith)
  unfold setupP
  refine WP.seq (WP.mono (enterP_ok hL hs hr) fun s₁ ⟨⟨p1, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (ptrP_ok (hs.congr k1.2.2) hL (hr.keepM k1 m1)) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ =>
    WP.mono (loadArr_ok (p1.env.keep k2) (j := 0) (N := key) (by decide)
      (by rw [a7]; exact (BitVec.add_zero _).symm) a8 (by omega) (by omega)
      (fun i hi => by rw [(k1.trans k2).2.1, (k1.trans k2).2.2]; exact hk.rd i (by omega))
      (fun i hi => hsepK i (by omega_arith))) fun s₃ ⟨⟨v0, top0, o3, a10⟩, k3⟩ => ?_))
  rw [m2, m1] at v0 o3
  have v0' : wordsVal s₃.mem L.S (slot L.wp 0) L.wp = pOf s.mem L key := v0
  have k13 := (k1.trans k2).trans k3
  have e3 : Env s₃ L.S L.qOff L.wp :=
    ⟨hs.p hL |>.congr k13.2.2, a10, ((k2.trans k3).gpr (by decide)).trans p1.env.s5,
      ((k2.trans k3).gpr (by decide)).trans p1.env.t0, p1.env.w2, p1.env.w48, p1.env.hZ⟩
  have hodd : (word s₃.mem L.S (slot L.wp 0)).toNat % 2 = 1 := by
    rw [wordsVal_mod_two _ _ _ (w := L.wp) (by omega), v0']; exact hpo
  refine WP.seq (WP.mono (minv_ok e3.hs e3.a7 (slot_al _ _) (by omega) hodd) fun s₄ ⟨⟨i4, m4⟩, k4⟩ => ?_)
  have e4 := e3.keep k4
  refine WP.mono (rr_ok e4 (by rw [m4, v0']; exact hp)) fun t ⟨⟨r1, r24, o5⟩, k5⟩ => ?_
  rw [m4, v0'] at r1 r24
  rw [m4] at o5
  have e5 := e4.keep k5
  refine ⟨⟨⟨e5, ((k2.trans k3 |>.trans k4 |>.trans k5).gpr (by decide)).trans p1.s6⟩, ?_, ?_, ?_, r1, r24, ?_⟩,
    ((k13.trans k4).trans k5).mono (by decide)⟩
  · rw [arrP, o5.wordsVal (by omega) (by omega_arith)]; exact v0'
  · rw [o5.word (by omega) (by omega_arith)]; exact top0
  · rw [o5.word (by omega) (by omega_arith), k5.gpr (by decide)]; exact i4
  · exact pbody_of_arrays o3 o5


/-! ## The domain's elements -/

theorem mask_clear (a b : Bool) : (mask a ||| mask b) ^^^ mask b = mask (a && !b) := by
  cases a <;> cases b <;> rfl

/-- `clear`: `a1 &= ¬a2`. -/
theorem clear_ok (s : State) {a b : Bool} (h1 : s.gpr .a1 = mask a) (h2 : s.gpr .a2 = mask b) :
    WP isa (.block clear) s fun t => (t.gpr .a1 = mask (a && !b) ∧ t.mem = s.mem) ∧ Keep [.a1] s t := by
  refine WP.keep _ ?_ (by decide) (by rfl)
  unfold clear
  brun [h1, h2, mask_clear]

/-- The registers `elemRange` writes. -/
def elemRangeRegs : List Reg := [.s0, .t3, .t5] ++ belowRegs ++ eqRegs .a2 ++ [.a0, .a1]

theorem slots_lt {w : Nat} : slot w 3 + 5 * (8 * (w + 2)) = slot w 8 := by simp only [Lay.slot_eq]; omega

/-- `elemRange`: `a0 = 0` exactly when `1 < [4] < [0]`, with `[4]`'s word `w`
zero; arrays 3, 5 and 7 change. -/
theorem elemRange_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w)
    (top : word s.mem B (slot w 4 + 8 * w) = 0) :
    WP isa elemRange s fun t =>
      ((t.gpr .a0 = 0 ↔ 1 < wordsVal s.mem B (slot w 4) w ∧ wordsVal s.mem B (slot w 4) w <
          wordsVal s.mem B (slot w 0) w) ∧
        wordsVal t.mem B (slot w 4) w = wordsVal s.mem B (slot w 4) w ∧
        Outside B (slot w 3) (5 * (8 * (w + 2))) s.mem t.mem ∧ Env t B Z w) ∧ Keep elemRangeRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw2 := h.w2
  have hw48 := h.w48
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e7 := e 7; have e8 := e 8; have e28 := e 28
  unfold elemRange
  refine WP.seq (WP.mono (Pub.oneP_ok hs (by omega) (by omega) (by omega) h.a7 h.s5 h.t0)
    fun s₁ ⟨⟨v7, o1'⟩, k1⟩ => ?_)
  have o1 : Outside B (slot w 7) (8 * w) s.mem s₁.mem := o1'
  have h1 := h.keep k1
  refine WP.seq (WP.mono (zeroArr_ok h1 (j := 5) (by decide)) fun s₂ ⟨⟨z5, o2⟩, k2⟩ => ?_)
  have h2 := h1.keep k2
  have top2 : word s₂.mem B (slot w 4 + 8 * w) = 0 := by
    rw [o2.word (by omega) (by omega_arith), o1.word (by omega) (by omega_arith)]; exact top
  have A4 : wordsVal s₂.mem B (slot w 4) w = wordsVal s.mem B (slot w 4) w := by
    rw [o2.wordsVal (by omega) (by omega_arith), o1.wordsVal (by omega) (by omega_arith)]
  have A0 : wordsVal s₂.mem B (slot w 0) w = wordsVal s.mem B (slot w 0) w := by
    rw [o2.wordsVal (by omega) (by omega_arith), o1.wordsVal (by omega) (by omega_arith)]
  have A7 : wordsVal s₂.mem B (slot w 7) w = 1 := by rw [o2.wordsVal (by omega) (by omega_arith)]; exact v7
  refine WP.seq (WP.mono (below_ok h2 (a := 4) (by decide) (by decide) top2) fun s₃ ⟨⟨b1, o3⟩, k3⟩ => ?_)
  rw [A4, A0] at b1
  have h3 := h2.keep k3
  have A4' : wordsVal s₃.mem B (slot w 4) w = wordsVal s.mem B (slot w 4) w := by
    rw [o3.wordsVal (by omega) (by omega_arith), A4]
  have A5 : wordsVal s₃.mem B (slot w 5) w = 0 := by rw [o3.wordsVal (by omega) (by omega_arith), z5]
  have A7' : wordsVal s₃.mem B (slot w 7) w = 1 := by rw [o3.wordsVal (by omega) (by omega_arith), A7]
  refine WP.seq (WP.mono (eqMask_ok h3 (j := 4) (k := 5) (rd := .a2) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨c2, m4⟩, k4⟩ => ?_)
  rw [A4', A5] at c2
  refine WP.seq (WP.mono (clear_ok s₄ ((k4.gpr (by decide)).trans b1) c2) fun s₅ ⟨⟨d1, m5⟩, k5⟩ => ?_)
  have h5 := h3.keep (k4.trans k5)
  have m35 : s₅.mem = s₃.mem := by rw [m5, m4]
  refine WP.seq (WP.mono (eqMask_ok h5 (j := 4) (k := 7) (rd := .a2) (by decide) (by decide) (by decide))
    fun s₆ ⟨⟨f2, m6⟩, k6⟩ => ?_)
  rw [m35, A4', A7'] at f2
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (clear_ok s₆ ((k6.gpr (by decide)).trans d1) f2) fun s₇ ⟨⟨g1, m7⟩, k7⟩ => ?_
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = s₇.gpr .a1 ∧ u.mem = s₇.mem)
    (by brun [BitVec.add_zero]) (by decide) (by rfl)) fun s₈ ⟨⟨a0, m8⟩, k8⟩ => ?_
  refine WP.mono (unmask_ok s₈ (a0.trans g1)) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have mt3 : t.mem = s₃.mem := by rw [mt, m8, m7, m6, m35]
  refine ⟨⟨?_, by rw [mt3]; exact A4', ?_, h5.keep ((k6.trans k7).trans (k8.trans kt))⟩,
    ((((k1.trans k2).trans k3).trans k4).trans (k5.trans ((k6.trans k7).trans (k8.trans kt)))).mono (by decide)⟩
  · rw [t0]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · rw [mt3]
    exact ((o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))).trans
      (o3.mono (by omega) (by omega))

/-- The registers `elemOrder` writes. -/
def elemOrderRegs : List Reg :=
  copyRegs ++ ptrRegs ++ [.s9, .s10] ++ Win.powWRegs ++ [.s0, .t3, .t5] ++ eqRegs .a0 ++ [.a0]

theorem pow_two_mul (w : Nat) : 2 ^ (64 * w) * 2 ^ (64 * w) = 2 ^ (128 * w) := by
  rw [← Nat.pow_add]; congr 1; omega

theorem p_win {L : Lay} {m m₁ m₂ m₃ : Mem} (o1 : Outside L.S (slot L.wp 1) (8 * (L.wp + 2)) m m₁)
    (o2 : Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) m₁ m₂)
    (o3 : Outside L.S (slot L.wp 7) (8 * L.wp) m₂ m₃) :
    Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) m m₃ :=
  ((o1.mono (Nat.le_refl _) (by omega)).trans o2).trans
    (o3.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega))

/-- `elemOrder`, in the P space with p (odd, at least 2) in array 0,
`-p⁻¹ mod 2⁶⁴` in `t1` and `R² mod p` in array 24: `a0 = 0` exactly when
`[4]^q mod p = 1`; arrays 1–23 change. -/
theorem elemOrder_ok {s : State} {L : Lay} {key sig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hin : InP s L) (hk : Src s L key (2 * L.pl + L.ql))
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1)
    (hinv : ((word s.mem L.S (slot L.wp 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa elemOrder s fun t =>
      ((t.gpr .a0 = 0 ↔ arrP s.mem L 4 ^ qOf s.mem L key % p = 1) ∧ InP t L ∧
        Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) s.mem t.mem) ∧ Keep elemOrderRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hnw := hL.nowrap
  have hbuf := hL.buf_end
  have hq0 := hL.qOff_eq
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e7 := e 7; have e8 := e 8; have e24 := e 24
  have e28 := e 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have hqZ : L.qOff ≤ L.Z := by have := hbuf; simp only [Lay.bOff] at this; omega
  have en := hin.env
  unfold elemOrder
  refine WP.seq (WP.mono (copy_ok en (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₁ ⟨⟨c1, o1⟩, k1⟩ => ?_)
  have A1 : wordsVal s₁.mem L.S (slot L.wp 1) L.wp = 2 ^ (128 * L.wp) % p := by
    rw [wordsVal_congr (m := s.mem) (d := slot L.wp 24) fun i hi => c1 i (by omega)]; exact hrr
  have A0 : wordsVal s₁.mem L.S (slot L.wp 0) L.wp = p := by
    rw [o1.wordsVal (by omega) (by omega_arith)]; exact hp0
  have A4 : wordsVal s₁.mem L.S (slot L.wp 4) L.wp = arrP s.mem L 4 := o1.wordsVal (by omega) (by omega_arith)
  have W0 : word s₁.mem L.S (slot L.wp 0) = word s.mem L.S (slot L.wp 0) := o1.word (by omega) (by omega_arith)
  have hb1 : Body L s.mem s₁.mem := Body.ofP hL o1 (by omega) (by omega)
  refine WP.seq (WP.block_append (WP.mono (ptrQ_ok (hs.congr k1.2.2) hL (hr.keep k1 hb1))
    fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off (off key L.pl) 0 ∧
      u.gpr .s10 = BitVec.ofNat 64 L.ql ∧ u.mem = s₂.mem) (by brun [a7, a8, BitVec.add_zero]) (by decide) (by rfl))
    fun s₃ ⟨⟨b9, b10, m3⟩, k3⟩ => ?_))
  have k13 := (k1.trans k2).trans k3
  have m31 : s₃.mem = s₁.mem := by rw [m3, m2]
  have e3 := en.keep k13
  refine WP.seq (WP.mono (Win.powWin_ok (D := off key L.pl) (L := L.ql) e3.hs (by omega) (by omega)
    (by omega) e3.a7 e3.s5 e3.t0 (by rw [m31, W0, k13.gpr (by decide)]; exact hinv)
    (by rw [m31, A0]; exact hp) (by rw [m31, A0]; exact hpo) (by rw [m31, A0, A1]; exact Nat.mod_lt _ (by omega))
    b9 b10 (by omega) (by omega_arith)
    (fun i hi => by
      have := hk.rd (L.pl + i) (by omega); rw [← off_off] at this; rw [k13.2.1, k13.2.2]; exact this)
    (fun i hi x hx => by
      have := hk.sep (L.pl + i) (by omega) x (Nat.lt_of_lt_of_le hx hqZ); rw [← off_off] at this; exact this))
    fun s₄ ⟨⟨r4, o4⟩, k4⟩ => ?_)
  rw [m31, A1, A0, A4, ← pow_two_mul] at r4
  have r4 := r4 rfl
  have hkq' : Spec.Rsa.bytesAt s₁.mem (off key L.pl) L.ql = Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql :=
    (hk.sub (o := L.pl) (k := L.ql) (by omega)).bytes hb1 (by omega)
  rw [hkq'] at r4
  rw [m31] at o4
  have e4 := e3.keep k4
  refine WP.seq (WP.mono (Pub.oneP_ok e4.hs (by omega) (by omega) (by omega) e4.a7 e4.s5 e4.t0)
    fun s₅ ⟨⟨v7, o5'⟩, k5⟩ => ?_)
  have o5 : Outside L.S (slot L.wp 7) (8 * L.wp) s₄.mem s₅.mem := o5'
  have e5 := e4.keep k5
  refine WP.seq (WP.mono (eqMask_ok e5 (j := 4) (k := 7) (rd := .a0) (by decide) (by decide) (by decide))
    fun s₆ ⟨⟨a0, m6⟩, k6⟩ => ?_)
  refine WP.mono (unmask_ok s₆ a0) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have A4' : wordsVal s₅.mem L.S (slot L.wp 4) L.wp = arrP s.mem L 4 ^ qOf s.mem L key % p := by
    rw [o5.wordsVal (by omega) (by omega_arith), r4]; rfl
  refine ⟨⟨?_, ⟨e5.keep (k6.trans kt), ((k13.trans ((k4.trans k5).trans (k6.trans kt))).gpr (by decide)).trans
    hin.s6⟩, by rw [mt, m6]; exact p_win o1 o4 o5⟩,
    (k13.trans ((k4.trans k5).trans (k6.trans kt))).mono (by decide)⟩
  rw [t0, decide_eq_true_iff, A4']
  rw [show wordsVal s₅.mem L.S (slot L.wp 7) L.wp = 1 from v7]

/-- The registers `checkElem` writes. -/
def elemRegs : List Reg := loadRegs ++ elemRangeRegs ++ elemOrderRegs

theorem p_elem {L : Lay} {m m₁ m₂ m₃ : Mem} (o1 : Outside L.S (slot L.wp 4) (8 * (L.wp + 1)) m m₁)
    (o2 : Outside L.S (slot L.wp 3) (5 * (8 * (L.wp + 2))) m₁ m₂)
    (o3 : Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) m₂ m₃) :
    Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) m m₃ :=
  ((o1.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega)).trans
    (o2.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega))).trans o3

theorem p_elem2 {L : Lay} {m m₁ m₂ : Mem} (o1 : Outside L.S (slot L.wp 4) (8 * (L.wp + 1)) m m₁)
    (o2 : Outside L.S (slot L.wp 3) (5 * (8 * (L.wp + 2))) m₁ m₂) :
    Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) m m₂ :=
  (o1.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega)).trans
    (o2.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega))

theorem p_arrays_body {L : Lay} (hL : L.Ok) {m m' : Mem}
    (o : Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) m m') : Body L m m' :=
  Body.ofP hL o (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.qOff, Lay.slot_eq]; omega)

/-- `checkElem`, in the P space with p (odd, at least 2) in array 0,
`-p⁻¹ mod 2⁶⁴` in `t1` and `R² mod p` in array 24: the `p_len` octets at `E`
(`s7`, `p_len` in `s8`) into array 4, and `a0 = 0` exactly when their number
`e` has `1 < e < p` and `e^q mod p = 1`; arrays 1–23 change. -/
theorem checkElem_ok {s : State} {L : Lay} {key sig E : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hin : InP s L) (hk : Src s L key (2 * L.pl + L.ql))
    (he : Src s L E L.pl) (h7 : s.gpr .s7 = E) (h8 : s.gpr .s8 = BitVec.ofNat 64 L.pl)
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1)
    (hinv : ((word s.mem L.S (slot L.wp 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa checkElem s fun t =>
      (InP t L ∧ (t.gpr .a0 = 0 ↔ (1 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) < p ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) ^ qOf s.mem L key % p = 1)) ∧
        Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) s.mem t.mem ∧ t.gpr .t1 = s.gpr .t1) ∧
        Keep elemRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hbuf := hL.buf_end
  have hqZ : L.qOff ≤ L.Z := by have := hbuf; simp only [Lay.bOff] at this; omega
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e24 := e 24; have e28 := e 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have en := hin.env
  unfold checkElem andThen
  refine WP.seq (WP.mono (loadArr_ok en (j := 4) (N := E) (by decide) (by rw [h7]; exact (BitVec.add_zero _).symm)
    h8 (by omega) (by omega) he.rd (fun i hi x hx => he.sep i hi x (Nat.lt_of_lt_of_le hx hqZ)))
    fun s₁ ⟨⟨v4, top4, o1, a7⟩, k1⟩ => ?_)
  have e1' : Env s₁ L.S L.qOff L.wp :=
    ⟨en.hs.congr k1.2.2, a7, (k1.gpr (by decide)).trans en.s5, (k1.gpr (by decide)).trans en.t0, en.w2, en.w48,
      en.hZ⟩
  have A0 : wordsVal s₁.mem L.S (slot L.wp 0) L.wp = p := by rw [o1.wordsVal (by omega) (by omega_arith)]; exact hp0
  refine WP.seq (WP.mono (elemRange_ok e1' top4) fun s₂ ⟨⟨r0, a4, o2, e2⟩, k2⟩ => ?_)
  rw [v4, A0] at r0
  have o12 := p_elem2 o1 o2
  have k12 := k1.trans k2
  refine WP.ite _ (Steps.eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · have hz := r0.mp (beq_iff_eq.mp hz)
    have hb2 : Body L s.mem s₂.mem := p_arrays_body hL o12
    refine WP.mono (elemOrder_ok (p := p) hL (hs.congr k12.2.2) (hr.keep k12 hb2)
      ⟨e2, (k12.gpr (by decide)).trans hin.s6⟩ ((hk.keep k12.2.1 k12.2.2))
      (by rw [arrP, o12.wordsVal (by omega) (by omega_arith)]; exact hp0) hp hpo
      (by rw [o12.word (by omega) (by omega_arith), k12.gpr (by decide)]; exact hinv)
      (by rw [arrP, o12.wordsVal (by omega) (by omega_arith)]; exact hrr))
      fun t ⟨⟨t0, ti, o3⟩, k3⟩ => ⟨⟨ti, ?_, p_elem o1 o2 o3, ?_⟩, k12.trans k3⟩
    · have A4 : arrP s₂.mem L 4 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) := by
        rw [arrP, a4]; exact v4
      have hq : qOf s₂.mem L key = qOf s.mem L key := by
        unfold qOf; rw [(hk.sub (o := L.pl) (k := L.ql) (by omega)).bytes hb2 (by omega)]
      rw [t0, A4, hq]
      exact ⟨fun h => ⟨hz.1, hz.2, h⟩, fun h => h.2.2⟩
    · rw [(k12.trans k3).gpr (by decide)]
  · refine WP.block_nil ⟨⟨⟨e2, (k12.gpr (by decide)).trans hin.s6⟩, ?_, o12, (k12.gpr (by decide))⟩,
      k12.mono fun r h => List.mem_append_left _ h⟩
    have hz : ¬ s₂.gpr .a0 = 0 := fun h => by simp [h] at hz
    exact ⟨fun h => absurd h hz, fun h => absurd (r0.mpr ⟨h.1, h.2.1⟩) hz⟩

end VG.Proof.Dsa.RISCV64
