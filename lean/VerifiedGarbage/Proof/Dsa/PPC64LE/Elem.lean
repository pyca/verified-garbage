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
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Prime
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Fast
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSan
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.Range
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# DSA on PPC64LE: `p mod q`, the P space, and the checks of g and y

* `setupQ_ok`: q into the Q space's array 0; `pModQ_ok`: the same, and
* `setupP_ok`: p into the P space's array 0 and `R² mod p` into its array 24
  (`Pre.r2Hi_ok` when p's top word is not zero, else `Pre.r2Prime_ok`);
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

/-- `setupQ`: into the Q space, and q into its array 0 (word 4 zero). -/
theorem setupQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hk : Src s L key (2 * L.pl + L.ql)) :
    WP isa setupQ s fun t =>
      (InQ t L ∧ arrQ t.mem L 0 = qOf s.mem L key ∧ word t.mem L.Q (slot 4 0 + 8 * 4) = 0 ∧
        QBody L s.mem t.mem) ∧ Keep pModQRegs s t := by
  have hbuf := hL.buf_end
  have hnw := hL.nowrap
  have hq0 := hL.qOff_eq
  have hpl := hL.pl
  have hql := hL.ql
  have hsepK : ∀ i < 2 * L.pl + L.ql, ∀ x, ofs L.Q x < 1600 → off key i ≠ x :=
    hk.sepIn (a := L.qOff) (by simp only [Lay.bOff] at hbuf; omega_arith) hnw
  unfold setupQ
  refine WP.seq (WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (ptrQ_ok (hr.keep k1)) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have hkq := (hk.sub (o := L.pl) (k := L.ql) (by omega_arith)).keep k12.rd k12.wr
  refine WP.mono (loadArr_ok (q1.env.keep k2 (by decide)) (j := 0) (by decide) a12 a6 (by omega_arith) (by omega_arith)
    hkq.rd (fun i hi => by rw [off_off]; exact hsepK _ (by omega_arith))) fun s₃ ⟨⟨v0, top0, o3, a10⟩, k3⟩ => ?_
  rw [m2, m1] at v0 o3
  have k23 := k2.trans k3
  exact ⟨⟨⟨env_keep10 (q1.env.keep k2 (by decide)) k3 (by decide) a10, (k23.gpr .r21 (by decide)).trans q1.h21,
    (k23.gpr .r23 (by decide)).trans q1.h23⟩, v0, top0, o3.mono (by decide) (by decide)⟩,
    (k12.trans k3).mono (by decide)⟩

/-- `pModQ`: into the Q space, q into its array 0 (word 4 zero), and `r0 = 0`
exactly when `p mod q = 1`. -/
theorem pModQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hk : Src s L key (2 * L.pl + L.ql))
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
  have hsepK : ∀ i < 2 * L.pl + L.ql, ∀ x, ofs L.Q x < 1600 → off key i ≠ x :=
    hk.sepIn (a := L.qOff) (by simp only [Lay.bOff] at hbuf; omega_arith) hnw
  unfold pModQ
  refine WP.seq (WP.mono (setupQ_ok hL hs hr hk) fun s₃ ⟨⟨q3, v0, top0, qb3⟩, k13⟩ => ?_)
  have e3 : Env s₃ L.Q 1600 4 := q3.env
  refine WP.seq (WP.mono (keyLen_ok (hr.keep k13)) fun s₄ ⟨⟨a30, a31, m4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  have v0' : arr s₃.mem L.Q 4 0 = qOf s.mem L key := v0
  refine WP.seq (WP.mono (ModArith.reduce_ok (D := key) (L := L.pl) (e3.hs.congr k4.wr) (by decide) (by decide)
    (by decide) ((k4.gpr .r10 (by decide)).trans e3.h10) ((k4.gpr .r29 (by decide)).trans e3.h29)
    ((k4.gpr .r11 (by decide)).trans e3.h11) (by rw [m4]; rw [arr] at v0'; rw [v0']; exact hq)
    (by rw [a30]; simp) a31 (by omega_arith)
    (by omega_arith) (fun i hi => by rw [k14.rd, k14.wr]; exact hk.rd i (by omega_arith)) (fun i hi => hsepK i (by omega_arith)))
    fun s₅ ⟨⟨r1, o5⟩, k5⟩ => ?_)
  rw [m4, hk.bytesPre (k := L.pl) (by omega_arith) (qb3.body hL) hZ] at r1
  have k15 := k14.trans k5
  have k25 := k4.trans k5
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = L.Q ∧ t.mem = s₅.mem) (by
      prun [(k25.gpr .r23 (by decide)).trans q3.h23, BitVec.add_zero]) (by decide)) fun s₆ ⟨⟨a31', m6⟩, k6⟩ => ?_)
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
    rw [Outside.val32 o7 (by rw [e, e]; omega_arith) (by rw [e]; omega_arith), m6, r1, ← arr, v0']; rfl
  refine ⟨⟨⟨e6.keep ((k7.trans k8).trans kt) (by decide),
    (k25.trans k6t).gpr .r21 (by decide) |>.trans q3.h21, (k25.trans k6t).gpr .r23 (by decide) |>.trans q3.h23⟩,
    ?_, ?_, ?_, ?_⟩, (k15.trans k6t).mono (by decide)⟩
  · show val32 t.mem L.Q (slot 4 0) (2 * 4) = _
    rw [hmt, Outside.val32 o7 (by rw [e, e]; omega_arith) (by rw [e]; omega_arith), m6,
      Outside.val32 o5 (by rw [e, e]; omega_arith) (by rw [e]; omega_arith), m4]; exact v0
  · rw [hmt, Outside.word o7 (by rw [e, e]; omega_arith) (by rw [e]; omega_arith), m6,
      Outside.word o5 (by rw [e, e]; omega_arith) (by rw [e]; omega_arith), m4]; exact top0
  · rw [t0, p1, v7, decide_eq_true_iff]
  · rw [m4] at o5'; rw [m6] at o7'; rw [hmt]; exact (qb3.trans o5').trans o7'

/-- A number of `2 w` 32-bit digits, split at its top 64-bit word. -/
theorem val32_top (m : Mem) (B : Addr) (d w : Nat) (hw : 1 ≤ w) :
    val32 m B d (2 * w) =
      val32 m B d (2 * (w - 1)) + 2 ^ (64 * (w - 1)) * (word m B (d + 8 * (w - 1))).toNat := by
  have h := val32_append m B d (2 * (w - 1)) 2
  rw [show 2 * (w - 1) + 2 = 2 * w by omega] at h
  rw [h, word_eq_w32, show 32 * (2 * (w - 1)) = 64 * (w - 1) by omega,
    show d + 4 * (2 * (w - 1)) = d + 8 * (w - 1) by omega]
  simp only [val32, Nat.mul_zero, Nat.add_zero]

/-- An odd number of `2 w` digits whose top 64-bit word is not zero is above
`2^(64 (w − 1))`. -/
theorem top_gt {m : Mem} {B : Addr} {d w N : Nat} (hw : 2 ≤ w) (hN : val32 m B d (2 * w) = N) (hodd : N % 2 = 1)
    (ht : word m B (d + 8 * (w - 1)) ≠ 0) : 2 ^ (64 * (w - 1)) < N := by
  have e := val32_top m B d w (by omega)
  have h1 : 1 ≤ (word m B (d + 8 * (w - 1))).toNat := by
    rcases Nat.eq_zero_or_pos (word m B (d + 8 * (w - 1))).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) ht
    · exact h
  have h2 : 2 ^ (64 * (w - 1)) ≤ N := by
    rw [← hN, e]; exact Nat.le_add_left_of_le (Nat.le_mul_of_pos_right _ h1)
  rcases Nat.lt_or_eq_of_le h2 with h | h
  · exact h
  · exfalso
    rw [← h, show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ] at hodd
    omega

/-- `topWord`: `r3 :=` the top 64-bit word of a number of `2 w` digits at
array 0 (`r10`), `r11 = 2 w`. -/
theorem topWord_ok {u : State} {B : Addr} {Z w : Nat} (hs : Scr u B Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (h10 : u.gpr .r10 = off B (slot w 0)) (h11 : u.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hZ : slot w 0 + 8 * w ≤ Z) :
    WP isa (.block topWord) u fun t =>
      (t.gpr .r3 = word u.mem B (slot w 0 + 8 * (w - 1)) ∧ t.mem = u.mem) ∧ Keep [.r3] u t := by
  have hnw := hs.nowrap
  have e0 := slot_eq w 0
  have hB := B.isLt
  have ha : off B (slot w 0 + 4 * (2 * w)) - 8#64 = off B (slot w 0 + 8 * (w - 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_arith
  unfold topWord
  refine WP.keep _ ?_ (by decide)
  prun [h10, h11, Pub.ofNat_shl2, ha, BitVec.add_zero, hs.ld (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega_arith)]

/-- The registers `setupPre` writes. -/
def setupPreRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r23, .r29, .r31]

/-- `setupPre`: into the P space, p into its array 0 (word `w` zero), `-p⁻¹ mod
2³²` into `r12`, the bases of arrays 1–3 into `r5`, `r8` and `r9`, and p's top
word into `r3`. Memory changes only in array 0. -/
theorem setupPre_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hk : Src s L key (2 * L.pl + L.ql)) (hpo : pOf s.mem L key % 2 = 1) :
    WP isa setupPre s fun t =>
      (InP t L ∧ t.gpr .r5 = off L.S (slot L.wp 1) ∧ t.gpr .r8 = off L.S (slot L.wp 2) ∧
        t.gpr .r9 = off L.S (slot L.wp 3) ∧ (t.gpr .r12).toNat < 2 ^ 32 ∧
        (w32 t.mem L.S (slot L.wp 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 ∧
        val32 t.mem L.S (slot L.wp 0) (2 * L.wp) = pOf s.mem L key ∧
        word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        Outside L.S (slot L.wp 0) (8 * (L.wp + 1)) s.mem t.mem ∧
        t.gpr .r3 = word t.mem L.S (slot L.wp 0 + 8 * (L.wp - 1))) ∧ Keep setupPreRegs s t := by
  have hZ := hL.hdr
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hqZ : L.qOff + 1600 ≤ L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith
  have e0 := slot_eq L.wp 0; have e28 := slot_eq L.wp 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold setupPre
  refine WP.seq (WP.mono (enterP_ok hL hs hr) fun s₁ ⟨⟨p1, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (ptrP_ok (hr.keep k1)) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_))
  have k12 := k1.trans k2
  refine WP.mono (loadArr_ok (p1.env.keep k2 (by decide)) (j := 0) (by decide) a12 a6 (by omega_arith) (by omega_arith)
    (fun i hi => by rw [k12.rd, k12.wr]; exact hk.rd i (by omega_arith))
    (fun i hi x hx => hk.sep i (by omega_arith) x (by omega_arith))) fun s₃ ⟨⟨v0, top0, o3, a10⟩, k3⟩ => ?_
  rw [m2, m1] at v0 o3
  have k13 := k12.trans k3
  have en3 : Env s₃ L.S L.qOff L.wp := env_keep10 (p1.env.keep k2 (by decide)) k3 (by decide) a10
  have v0p : val32 s₃.mem L.S (slot L.wp 0) (2 * L.wp) = pOf s.mem L key := v0
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  -- `-p⁻¹ mod 2³²`.
  have hlow : (word s₃.mem L.S (slot L.wp 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₃.mem L.S (slot L.wp 0)
    have h2 : val32 s₃.mem L.S (slot L.wp 0) (2 * L.wp - 1 + 1) =
        w32 s₃.mem L.S (slot L.wp 0) + 2 ^ 32 * val32 s₃.mem L.S (slot L.wp 0 + 4) (2 * L.wp - 1) := rfl
    rw [Nat.sub_add_cancel (by omega_arith : 1 ≤ 2 * L.wp), v0p] at h2
    omega_arith
  refine WP.mono (Pub.minv_ok en3.hs en3.h10 (by omega_arith) hlow) fun s₃' ⟨⟨r12lt, r12inv, m3'⟩, k3'⟩ => ?_
  have en3' := en3.keep k3' (by decide)
  refine WP.mono (en3'.base (rd := .r5) (by decide) (by decide) 1) fun s₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  have en4 := en3'.keep k4 (by decide)
  refine WP.mono (en4.base (rd := .r8) (by decide) (by decide) 2) fun s₅ ⟨⟨a8, m5⟩, k5⟩ => ?_
  have en5 := en4.keep k5 (by decide)
  refine WP.mono (en5.base (rd := .r9) (by decide) (by decide) 3) fun s₆ ⟨⟨a9, m6⟩, k6⟩ => ?_
  have en6 := en5.keep k6 (by decide)
  have hm6 : s₆.mem = s₃.mem := by rw [m6, m5, m4, m3']
  refine WP.mono (topWord_ok en6.hs (by omega_arith) (by omega_arith) en6.h10 en6.h11 (by omega_arith))
    fun t ⟨⟨a3, mt⟩, kt⟩ => ?_
  have k4t := ((((k3'.trans k4).trans k5).trans k6).trans kt)
  have hmt : t.mem = s₃.mem := by rw [mt, hm6]
  refine ⟨⟨⟨en6.keep kt (by decide), ((k2.trans k3).trans k4t).gpr .r21 (by decide) |>.trans p1.h21,
    ((k2.trans k3).trans k4t).gpr .r23 (by decide) |>.trans p1.h23⟩,
    by rw [kt.gpr .r5 (by decide), k6.gpr .r5 (by decide), k5.gpr .r5 (by decide)]; exact a5,
    by rw [kt.gpr .r8 (by decide), k6.gpr .r8 (by decide)]; exact a8,
    by rw [kt.gpr .r9 (by decide)]; exact a9,
    by rw [kt.gpr .r12 (by decide), k6.gpr .r12 (by decide), k5.gpr .r12 (by decide), k4.gpr .r12 (by decide)]; exact r12lt,
    by rw [kt.gpr .r12 (by decide), k6.gpr .r12 (by decide), k5.gpr .r12 (by decide), k4.gpr .r12 (by decide), hmt]
       exact r12inv,
    by rw [hmt]; exact v0, by rw [hmt]; exact top0, by rw [hmt]; exact o3, by rw [a3, mt, hm6]⟩,
    (k13.trans k4t).mono (by decide)⟩

/-- The registers `setupP` writes. -/
def setupPRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22,
    .r23, .r24, .r29, .r31]

/-- One branch of `setupP`: `R² mod N` into array 1 by `c` (which writes only
arrays 1–24 and `rs`), then into array 24. -/
theorem setupTail_ok {u : State} {L : Lay} {N : Nat} {c : Prog isa} {rs : List Reg} (hL : L.Ok) (hin : InP u L)
    (hrs : ∀ r ∈ rs, r ∈ setupPRegs) (hrsE : ∀ r ∈ ([.r10, .r11, .r21, .r23, .r29, .r31] : List Reg), r ∉ rs)
    (hc : WP isa c u fun t => val32 t.mem L.S (slot L.wp 1) (2 * L.wp) = 2 ^ (128 * L.wp) % N ∧
      Outside L.S (slot L.wp 1) (24 * (L.wp + 2)) u.mem t.mem ∧ Keep rs u t) :
    WP isa (.seq c (VG.Impl.MillerRabin.PPC64LE.copy 24 1)) u fun t =>
      (InP t L ∧ arrP t.mem L 0 = arrP u.mem L 0 ∧
        word t.mem L.S (slot L.wp 0 + 8 * L.wp) = word u.mem L.S (slot L.wp 0 + 8 * L.wp) ∧
        arrP t.mem L 24 = 2 ^ (128 * L.wp) % N ∧
        Outside L.S (slot L.wp 1) (L.qOff - slot L.wp 1) u.mem t.mem) ∧ Keep setupPRegs u t := by
  have hw := hL.wp_ge
  have hnw := hL.nowrap
  have hqZ : L.qOff + 1600 ≤ L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith
  have e0 := slot_eq L.wp 0; have e1 := slot_eq L.wp 1; have e24 := slot_eq L.wp 24; have e28 := slot_eq L.wp 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  refine WP.seq (WP.mono hc fun s₇ ⟨hr2, o7, k7⟩ => ?_)
  have en7 : Env s₇ L.S L.qOff L.wp :=
    ⟨hin.env.hs.congr k7.wr, (k7.gpr _ (hrsE _ (by decide))).trans hin.env.h10,
      (k7.gpr _ (hrsE _ (by decide))).trans hin.env.h29, (k7.gpr _ (hrsE _ (by decide))).trans hin.env.h11,
      (k7.gpr _ (hrsE _ (by decide))).trans hin.env.h31, hin.env.hw, hin.env.hw', hin.env.hZ⟩
  refine WP.mono (copy_ok en7 (o := 24) (a := 1) (by decide) (by decide) (by decide)) fun t ⟨⟨v8, o8⟩, kt⟩ => ?_
  refine ⟨⟨⟨en7.keep kt (by decide), (kt.gpr .r21 (by decide)).trans ((k7.gpr _ (hrsE _ (by decide))).trans hin.h21),
    (kt.gpr .r23 (by decide)).trans ((k7.gpr _ (hrsE _ (by decide))).trans hin.h23)⟩, ?_, ?_, v8.trans hr2, ?_⟩,
    (k7.trans kt).mono fun r hr => ?_⟩
  · show val32 t.mem L.S (slot L.wp 0) (2 * L.wp) = val32 u.mem L.S (slot L.wp 0) (2 * L.wp)
    rw [Outside.val32 o8 (by omega_arith) (by omega_arith), Outside.val32 o7 (by omega_arith) (by omega_arith)]
  · rw [Outside.word o8 (by omega_arith) (by omega_arith), Outside.word o7 (by omega_arith) (by omega_arith)]
  · exact (o7.mono (by omega_arith) (by omega_arith)).trans (o8.mono (by omega_arith) (by omega_arith))
  · rcases List.mem_append.mp hr with hr | hr
    · exact hrs r hr
    · exact (by decide : ∀ r ∈ copyRegs, r ∈ setupPRegs) r hr

/-- `setupP`: into the P space, p into its array 0 (word `w` zero) and
`R² mod p` (`R = 2^(64 w)`) into its array 24, by `r2Hi` when p's top word is
not zero, else `r2Prime`. -/
theorem setupP_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hk : Src s L key (2 * L.pl + L.ql))
    (hp : 2 ≤ pOf s.mem L key) (hpo : pOf s.mem L key % 2 = 1) :
    WP isa setupP s fun t =>
      (InP t L ∧ arrP t.mem L 0 = pOf s.mem L key ∧ word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        arrP t.mem L 24 = 2 ^ (128 * L.wp) % pOf s.mem L key ∧ PBody L s.mem t.mem) ∧
        Keep setupPRegs s t := by
  have hw := hL.wp_ge
  have hnw := hL.nowrap
  have hqZ : L.qOff + 1600 ≤ L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith
  have e0 := slot_eq L.wp 0; have e1 := slot_eq L.wp 1; have e8 := slot_eq L.wp 8; have e24 := slot_eq L.wp 24
  have e28 := slot_eq L.wp 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold setupP
  refine WP.seq (WP.mono (setupPre_ok hL hs hr hk hpo)
    fun u ⟨⟨hin, a5, a8, a9, r12lt, r12inv, v0, top0, o3, a3⟩, ku⟩ => ?_)
  have fin : ∀ t, ((InP t L ∧ arrP t.mem L 0 = arrP u.mem L 0 ∧
        word t.mem L.S (slot L.wp 0 + 8 * L.wp) = word u.mem L.S (slot L.wp 0 + 8 * L.wp) ∧
        arrP t.mem L 24 = 2 ^ (128 * L.wp) % pOf s.mem L key ∧
        Outside L.S (slot L.wp 1) (L.qOff - slot L.wp 1) u.mem t.mem) ∧ Keep setupPRegs u t) →
      (InP t L ∧ arrP t.mem L 0 = pOf s.mem L key ∧ word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        arrP t.mem L 24 = 2 ^ (128 * L.wp) % pOf s.mem L key ∧ PBody L s.mem t.mem) ∧ Keep setupPRegs s t :=
    fun t ⟨⟨it, a0, w0, a24, ot⟩, kt⟩ =>
      ⟨⟨it, a0.trans v0, w0.trans top0, a24,
        (o3.mono (by omega_arith) (by omega_arith)).trans (ot.mono (by omega_arith) (by omega_arith))⟩,
        (ku.trans kt).mono (by decide)⟩
  refine WP.ite (u.gpr .r3 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · refine WP.mono (setupTail_ok (N := pOf s.mem L key) (rs := Pre.r2PrimeRegs) hL hin (by decide) (by decide)
      (WP.mono (Pre.r2Prime_ok hin.env.hs a8 a9 hin.env.h10 a5 hin.env.h11 (by omega_arith) (by omega_arith)
        (by omega_arith) r12lt r12inv (by rw [v0]; exact hp) (by rw [v0]; exact hpo))
        fun t ⟨h1, h2, h3⟩ => ⟨by rw [h1, v0], h2, h3⟩)) fin
  · have hne : word u.mem L.S (slot L.wp 0 + 8 * (L.wp - 1)) ≠ 0 := by
      rw [← a3]; simpa using hb
    refine WP.mono (setupTail_ok (N := pOf s.mem L key) (rs := Pre.hiRegs) hL hin (by decide) (by decide)
      (WP.mono (Pre.r2Hi_ok hin.env.hs a8 a9 hin.env.h10 a5 hin.env.h11 (by omega_arith) (by omega_arith)
        (by omega_arith) r12lt r12inv v0 (top_gt (by omega_arith) v0 hpo hne) hpo)
        fun t ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩)) fin

/-- The registers `checkElem` writes. -/
def elemRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24,
    .r25, .r30, .r31]

/-- `checkElem`, in the P space with p in array 0 and `R² mod p` in array 24:
the `p_len` octets at `E` (`r12`, `p_len` in `r6`) into array 4, and `r0 = 0`
exactly when their number `e` has `1 < e < p` and `e^q mod p = 1`. Arrays 0
and 24 are kept. -/
theorem checkElem_ok {s : State} {L : Lay} {key sig dig E : Addr} {p : Nat} (hL : L.Ok)
    (hr : Regs s L key sig dig) (hin : InP s L) (hk : Src s L key (2 * L.pl + L.ql))
    (he : Src s L E L.pl) (h12 : s.gpr .r12 = E) (h6 : s.gpr .r6 = BitVec.ofNat 64 L.pl)
    (hp0 : arrP s.mem L 0 = p) (hz0 : word s.mem L.S (slot L.wp 0 + 8 * L.wp) = 0) (hp : 2 ≤ p)
    (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa checkElem s fun t =>
      (InP t L ∧ arrP t.mem L 0 = p ∧ word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        arrP t.mem L 24 = arrP s.mem L 24 ∧
        (t.gpr .r0 = 0 ↔ (1 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) < p ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) ^ qOf s.mem L key % p = 1)) ∧
        PBody L s.mem t.mem) ∧
        Keep elemRegs s t := by
  have hZ := hL.hdr
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hqZ : L.qOff + 1600 ≤ L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have e0 := slot_eq L.wp 0; have e1 := slot_eq L.wp 1; have e3 := slot_eq L.wp 3; have e4 := slot_eq L.wp 4
  have e8 := slot_eq L.wp 8; have e24 := slot_eq L.wp 24; have e28 := slot_eq L.wp 28
  have en := hin.env
  unfold checkElem andThen
  refine WP.seq (WP.mono (loadArr_ok en (j := 4) (by decide) h12 h6 (by omega_arith) (by omega_arith) he.rd
    (fun i hi x hx => he.sep i hi x (Nat.lt_of_lt_of_le hx (by omega_arith)))) fun s₁ ⟨⟨v4, top4, o1, a10⟩, k1⟩ => ?_)
  have en1 := env_keep10 en k1 (by decide) a10
  have pb1 : PBody L s.mem s₁.mem := o1.mono (by omega_arith) (by omega_arith)
  have p1 : arr s₁.mem L.S L.wp 0 = p := by rw [arr, Outside.val32 o1 (by omega_arith) (by omega_arith)]; exact hp0
  refine WP.seq (WP.mono (elemRange_ok en1 top4) fun s₂ ⟨⟨r0i, a4, o2, en2⟩, k2⟩ => ?_)
  have pb2 : PBody L s₁.mem s₂.mem := o2.mono (by omega_arith) (by omega_arith)
  have pb12 := pb1.trans pb2
  have p2 : arr s₂.mem L.S L.wp 0 = p := by rw [arr, Outside.val32 o2 (by omega_arith) (by omega_arith)]; exact p1
  have z2 : word s₂.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 := by
    rw [Outside.word o2 (by omega_arith) (by omega_arith), Outside.word o1 (by omega_arith) (by omega_arith)]; exact hz0
  have r2 : arrP s₂.mem L 24 = arrP s.mem L 24 := by
    show val32 s₂.mem L.S (slot L.wp 24) (2 * L.wp) = _
    rw [Outside.val32 o2 (by omega_arith) (by omega_arith), Outside.val32 o1 (by omega_arith) (by omega_arith)]
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
      rw [Outside.val32 o3 (by omega_arith) (by omega_arith)]; exact p2
    · rw [Outside.word o3 (by omega_arith) (by omega_arith)]; exact z2
    · show val32 t.mem L.S (slot L.wp 24) (2 * L.wp) = _
      rw [Outside.val32 o3 (by omega_arith) (by omega_arith)]; exact r2
    · have hq : qOf s₂.mem L key = qOf s.mem L key :=
        congrArg Spec.Dsa.decodeBE ((hk.sub (o := L.pl) (k := L.ql) (by omega_arith)).bytesPre (Nat.le_refl _)
          (pb12.body hL) hZ)
      have a4' : arrP s₂.mem L 4 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) := a4.trans x1
      rw [t0, a4', hq]
      exact ⟨fun h => ⟨hrg.1, hrg.2, h⟩, fun h => h.2.2⟩
    · exact pb12.trans (o3.mono (by omega_arith) (by omega_arith))
  · have h0 : s₂.gpr .r0 ≠ 0 := by simpa using hb
    exact WP.block_nil ⟨⟨in2, p2, z2, r2, ⟨fun h => absurd h h0, fun h => absurd (r0i.mpr ⟨h.1, h.2.1⟩) h0⟩,
      pb12⟩, k12.mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE
