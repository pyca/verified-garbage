module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
public import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
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


end VG.Proof.Dsa.RISCV64
