module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Basic
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Check
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.Range
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# DSA on PPC64LE: `p mod q`, the P space, and the checks of g and y

* `pModQ_ok`: q into the Q space's array 0, and `r0 = 0` exactly when
  `p mod q = 1`;
* `setupP_ok`: p into the P space's array 0 and `R² mod p` into its array 8;
* `checkElem_ok`: a number of `p_len` octets into the P space's array 4, and
  `r0 = 0` exactly when it is above 1, below p, and its q-th power modulo p
  is 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- The registers `pModQ` writes. -/
def pModQRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r20, .r23, .r24, .r25, .r29,
    .r30, .r31]

/-- `pModQ`: into the Q space, q into its array 0 (word 4 zero), and `r0 = 0`
exactly when `p mod q = 1`. -/
theorem pModQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hk : Src s L key (3 * L.pl + L.ql))
    (hq : 0 < qOf s.mem L key) :
    WP isa pModQ s fun t =>
      (InQ t L ∧ arrQ t.mem L 0 = qOf s.mem L key ∧ word t.mem L.Q (slot 4 0 + 8 * 4) = 0 ∧
        (t.gpr .r0 = 0 ↔ pOf s.mem L key % qOf s.mem L key = 1) ∧ QBody L s.mem t.mem) ∧
        Keep pModQRegs s t := by
  have hZ := hL.hdr
  have hbuf := hL.buf_end
  have hnw := hL.nowrap
  have hq0 := hL.qOff_eq
  have hpl := hL.pl
  have hql := hL.ql
  have e : ∀ j, slot 4 j = 256 + j * 48 := fun _ => rfl
  have hsepK : ∀ i < 3 * L.pl + L.ql, ∀ x, ofs L.Q x < 1600 → off key i ≠ x :=
    hk.sepIn (a := L.qOff) (by simp only [Lay.bOff] at hbuf; omega) hnw
  unfold pModQ
  refine WP.seq (WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (ptrQ_ok (hr.keep k1))
    fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_))
  have k12 := k1.trans k2
  have hkq := (hk.sub (o := L.pl) (k := L.ql) (by omega)).keep k12.rd k12.wr
  refine WP.mono (loadArr_ok (q1.env.keep k2 (by decide)) (j := 0) (by decide) a12 a6 (by omega) (by omega)
    hkq.rd (fun i hi => by rw [off_off]; exact hsepK _ (by omega))) fun s₃ ⟨⟨v0, top0, o3, a10⟩, k3⟩ => ?_
  rw [m2, m1] at v0 o3
  have k13 := k12.trans k3
  have e3 : Env s₃ L.Q 1600 4 := env_keep10 (q1.env.keep k2 (by decide)) k3 (by decide) a10
  have qb3 : QBody L s.mem s₃.mem := o3.mono (by decide) (by decide)
  refine WP.seq (WP.mono (keyLen_ok (hr.keep k13)) fun s₄ ⟨⟨a30, a31, m4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  have v0' : arr s₃.mem L.Q 4 0 = qOf s.mem L key := v0
  refine WP.seq (WP.mono (ModArith.reduce_ok (D := key) (L := L.pl) (e3.hs.congr k4.wr) (by decide) (by decide)
    (by decide) ((k4.gpr .r10 (by decide)).trans e3.h10) ((k4.gpr .r29 (by decide)).trans e3.h29)
    ((k4.gpr .r11 (by decide)).trans e3.h11) (by rw [m4]; rw [arr] at v0'; rw [v0']; exact hq)
    (by rw [a30]; simp) a31 (by omega)
    (by omega) (fun i hi => by rw [k14.rd, k14.wr]; exact hk.rd i (by omega)) (fun i hi => hsepK i (by omega)))
    fun s₅ ⟨⟨r1, o5⟩, k5⟩ => ?_)
  rw [m4, hk.bytesPre (k := L.pl) (by omega) (qb3.body hL) hZ] at r1
  have k15 := k14.trans k5
  have k25 := ((k2.trans k3).trans k4).trans k5
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = L.Q ∧ t.mem = s₅.mem) (by
      prun [(k25.gpr .r23 (by decide)).trans q1.h23, BitVec.add_zero]) (by decide)) fun s₆ ⟨⟨a31', m6⟩, k6⟩ => ?_)
  have e6 := env_keep31 e3 ((k4.trans k5).trans k6) (by decide) a31'
  refine WP.seq (WP.mono (Pub.oneP_ok e6.hs (by decide) (by decide) (by decide) e6.h10 e6.h29 e6.h11)
    fun s₇ ⟨⟨v7, o7⟩, k7⟩ => ?_)
  have e7 := e6.keep k7 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e7 .r3 (a := 1) (b := 7) (by decide) (by decide)) fun s₈ ⟨⟨a3, m8⟩, k8⟩ => ?_)
  refine WP.mono (unmask_ok s₈ a3) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have k6t := ((k6.trans k7).trans k8).trans kt
  have o5' : QBody L s₄.mem s₅.mem := o5.mono (by decide) (by decide)
  have o7' : QBody L s₆.mem s₇.mem := o7.mono (by decide) (by decide)
  have hmt : t.mem = s₇.mem := by rw [mt, m8]
  have p1 : val32 s₇.mem L.Q (slot 4 1) (2 * 4) = pOf s.mem L key % qOf s.mem L key := by
    rw [Outside.val32 o7 (by rw [e, e]; omega) (by rw [e]; omega), m6, r1, ← arr, v0']; rfl
  refine ⟨⟨⟨e6.keep ((k7.trans k8).trans kt) (by decide),
    (k25.trans k6t).gpr .r21 (by decide) |>.trans q1.h21, (k25.trans k6t).gpr .r23 (by decide) |>.trans q1.h23⟩,
    ?_, ?_, ?_, ?_⟩, (k15.trans k6t).mono (by decide)⟩
  · show val32 t.mem L.Q (slot 4 0) (2 * 4) = _
    rw [hmt, Outside.val32 o7 (by rw [e, e]; omega) (by rw [e]; omega), m6,
      Outside.val32 o5 (by rw [e, e]; omega) (by rw [e]; omega), m4]; exact v0
  · rw [hmt, Outside.word o7 (by rw [e, e]; omega) (by rw [e]; omega), m6,
      Outside.word o5 (by rw [e, e]; omega) (by rw [e]; omega), m4]; exact top0
  · rw [t0, p1, v7, decide_eq_true_iff]
  · rw [m4] at o5'; rw [m6] at o7'; rw [hmt]; exact (qb3.trans o5').trans o7'

/-- The registers `setupP` writes. -/
def setupPRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r20, .r23, .r29, .r31]

/-- `setupP`: into the P space, p into its array 0 (word `w` zero) and
`R² mod p` (`R = 2^(64 w)`) into its array 8. -/
theorem setupP_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hk : Src s L key (3 * L.pl + L.ql))
    (hp : 2 ≤ pOf s.mem L key) :
    WP isa setupP s fun t =>
      (InP t L ∧ arrP t.mem L 0 = pOf s.mem L key ∧ word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        arrP t.mem L 8 = 2 ^ (128 * L.wp) % pOf s.mem L key ∧ PBody L s.mem t.mem) ∧
        Keep setupPRegs s t := by
  have hZ := hL.hdr
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hqZ : L.qOff + 1600 ≤ L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega
  have e0 := slot_eq L.wp 0; have e1 := slot_eq L.wp 1; have e2 := slot_eq L.wp 2; have e3 := slot_eq L.wp 3
  have e4 := slot_eq L.wp 4; have e8 := slot_eq L.wp 8; have e28 := slot_eq L.wp 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold setupP
  refine WP.seq (WP.mono (enterP_ok hL hs hr) fun s₁ ⟨⟨p1, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (ptrP_ok (hr.keep k1)) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_))
  have k12 := k1.trans k2
  refine WP.mono (loadArr_ok (p1.env.keep k2 (by decide)) (j := 0) (by decide) a12 a6 (by omega) (by omega)
    (fun i hi => by rw [k12.rd, k12.wr]; exact hk.rd i (by omega))
    (fun i hi x hx => hk.sep i (by omega) x (by omega))) fun s₃ ⟨⟨v0, top0, o3, a10⟩, k3⟩ => ?_
  rw [m2, m1] at v0 o3
  have k13 := k12.trans k3
  have en3 : Env s₃ L.S L.qOff L.wp := env_keep10 (p1.env.keep k2 (by decide)) k3 (by decide) a10
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (en3.base (rd := .r5) (by decide) (by decide) 1) fun s₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  have en4 := en3.keep k4 (by decide)
  refine WP.mono (en4.base (rd := .r8) (by decide) (by decide) 2) fun s₅ ⟨⟨a8, m5⟩, k5⟩ => ?_
  have en5 := en4.keep k5 (by decide)
  refine WP.mono (en5.base (rd := .r9) (by decide) (by decide) 3) fun s₆ ⟨⟨a9, m6⟩, k6⟩ => ?_
  have en6 := en5.keep k6 (by decide)
  have hm6 : s₆.mem = s₃.mem := by rw [m6, m5, m4]
  have v0' : val32 s₆.mem L.S (slot L.wp 0) (2 * L.wp) = pOf s.mem L key := by rw [hm6]; exact v0
  refine WP.seq (WP.mono (r2_ok en6.hs ((k6.gpr .r8 (by decide)).trans a8) a9 en6.h10
    ((k6.gpr .r5 (by decide)).trans ((k5.gpr .r5 (by decide)).trans a5)) en6.h11 (by omega) (by omega)
    (by omega) (by rw [v0']; exact hp)) fun s₇ ⟨hr2, o7, k7⟩ => ?_)
  rw [v0'] at hr2
  have en7 := en6.keep k7 (by decide)
  refine WP.mono (copy_ok en7 (o := 8) (a := 1) (by decide) (by decide) (by decide)) fun t ⟨⟨v8, o8⟩, kt⟩ => ?_
  have k4t := ((((k4.trans k5).trans k6).trans k7).trans kt)
  refine ⟨⟨⟨en7.keep kt (by decide), ((k2.trans k3).trans k4t).gpr .r21 (by decide) |>.trans p1.h21,
    ((k2.trans k3).trans k4t).gpr .r23 (by decide) |>.trans p1.h23⟩, ?_, ?_, ?_, ?_⟩,
    (k13.trans k4t).mono (by decide)⟩
  · show val32 t.mem L.S (slot L.wp 0) (2 * L.wp) = _
    rw [Outside.val32 o8 (by omega) (by omega), Outside.val32 o7 (by omega) (by omega), hm6]; exact v0
  · rw [Outside.word o8 (by omega) (by omega), Outside.word o7 (by omega) (by omega), hm6]; exact top0
  · exact v8.trans hr2
  · rw [hm6] at o7
    exact ((o3.mono (by omega) (by omega)).trans (o7.mono (by omega) (by omega))).trans (o8.mono (by omega) (by omega))

/-- The registers `checkElem` writes. -/
def elemRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24,
    .r25, .r30, .r31]

/-- `checkElem`, in the P space with p in array 0 and `R² mod p` in array 8:
the `p_len` octets at `E` (`r12`, `p_len` in `r6`) into array 4, and `r0 = 0`
exactly when their number `e` has `1 < e < p` and `e^q mod p = 1`. Arrays 0
and 8 are kept. -/
theorem checkElem_ok {s : State} {L : Lay} {key sig dig E : Addr} {p : Nat} (hL : L.Ok)
    (hr : Regs s L key sig dig) (hin : InP s L) (hk : Src s L key (3 * L.pl + L.ql))
    (he : Src s L E L.pl) (h12 : s.gpr .r12 = E) (h6 : s.gpr .r6 = BitVec.ofNat 64 L.pl)
    (hp0 : arrP s.mem L 0 = p) (hz0 : word s.mem L.S (slot L.wp 0 + 8 * L.wp) = 0) (hp : 2 ≤ p)
    (hpo : p % 2 = 1) (hrr : arrP s.mem L 8 = 2 ^ (128 * L.wp) % p) :
    WP isa checkElem s fun t =>
      (InP t L ∧ arrP t.mem L 0 = p ∧ word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        arrP t.mem L 8 = arrP s.mem L 8 ∧
        (t.gpr .r0 = 0 ↔ (1 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) < p ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) ^ qOf s.mem L key % p = 1)) ∧
        PBody L s.mem t.mem) ∧
        Keep elemRegs s t := by
  have hZ := hL.hdr
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hqZ : L.qOff + 1600 ≤ L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have e0 := slot_eq L.wp 0; have e1 := slot_eq L.wp 1; have e3 := slot_eq L.wp 3; have e4 := slot_eq L.wp 4
  have e8 := slot_eq L.wp 8; have e28 := slot_eq L.wp 28
  have en := hin.env
  unfold checkElem andThen
  refine WP.seq (WP.mono (loadArr_ok en (j := 4) (by decide) h12 h6 (by omega) (by omega) he.rd
    (fun i hi x hx => he.sep i hi x (Nat.lt_of_lt_of_le hx (by omega)))) fun s₁ ⟨⟨v4, top4, o1, a10⟩, k1⟩ => ?_)
  have en1 := env_keep10 en k1 (by decide) a10
  have pb1 : PBody L s.mem s₁.mem := o1.mono (by omega) (by omega)
  have p1 : arr s₁.mem L.S L.wp 0 = p := by rw [arr, Outside.val32 o1 (by omega) (by omega)]; exact hp0
  refine WP.seq (WP.mono (elemRange_ok en1 top4) fun s₂ ⟨⟨r0i, a4, o2, en2⟩, k2⟩ => ?_)
  have pb2 : PBody L s₁.mem s₂.mem := o2.mono (by omega) (by omega)
  have pb12 := pb1.trans pb2
  have p2 : arr s₂.mem L.S L.wp 0 = p := by rw [arr, Outside.val32 o2 (by omega) (by omega)]; exact p1
  have z2 : word s₂.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 := by
    rw [Outside.word o2 (by omega) (by omega), Outside.word o1 (by omega) (by omega)]; exact hz0
  have r2 : arrP s₂.mem L 8 = arrP s.mem L 8 := by
    show val32 s₂.mem L.S (slot L.wp 8) (2 * L.wp) = _
    rw [Outside.val32 o2 (by omega) (by omega), Outside.val32 o1 (by omega) (by omega)]
  have x1 : arr s₁.mem L.S L.wp 4 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) := v4
  rw [x1, p1] at r0i
  have k12 := k1.trans k2
  have in2 : InP s₂ L := ⟨en2, (k12.gpr .r21 (by decide)).trans hin.h21, (k12.gpr .r23 (by decide)).trans hin.h23⟩
  refine WP.ite (s₂.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hrg := r0i.mp (beq_iff_eq.mp hb)
    refine WP.mono (elemOrder_ok hL (hr.keep k12) in2 (hk.keep k12.rd k12.wr)
      p2 hp hpo (by rw [r2]; exact hrr)) fun t ⟨⟨t0, int, o3⟩, k3⟩ =>
        ⟨⟨int, ?_, ?_, ?_, ?_, ?_⟩, (k12.trans k3).mono (by decide)⟩
    · show val32 t.mem L.S (slot L.wp 0) (2 * L.wp) = p
      rw [Outside.val32 o3 (by omega) (by omega)]; exact p2
    · rw [Outside.word o3 (by omega) (by omega)]; exact z2
    · show val32 t.mem L.S (slot L.wp 8) (2 * L.wp) = _
      rw [Outside.val32 o3 (by omega) (by omega)]; exact r2
    · have hq : qOf s₂.mem L key = qOf s.mem L key :=
        congrArg Spec.Dsa.decodeBE ((hk.sub (o := L.pl) (k := L.ql) (by omega)).bytesPre (Nat.le_refl _)
          (pb12.body hL) hZ)
      have a4' : arrP s₂.mem L 4 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) := a4.trans x1
      rw [t0, a4', hq]
      exact ⟨fun h => ⟨hrg.1, hrg.2, h⟩, fun h => h.2.2⟩
    · exact pb12.trans (o3.mono (by omega) (by omega))
  · have h0 : s₂.gpr .r0 ≠ 0 := by simpa using hb
    exact WP.block_nil ⟨⟨in2, p2, z2, r2, ⟨fun h => absurd h h0, fun h => absurd (r0i.mpr ⟨h.1, h.2.1⟩) h0⟩,
      pb12⟩, k12.mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE
