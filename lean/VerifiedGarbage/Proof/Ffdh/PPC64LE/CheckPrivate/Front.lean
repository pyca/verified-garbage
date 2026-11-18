module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Range
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont

/-! ### `Ffdh.PPC64LE.CheckPrivate.Status`, which the modules that import this one used -/

section

/-! ### `Ffdh.PPC64LE.CheckPrivate.Body`, which this module and modules that import it used -/

section

/-!
# `vg_ffdh_check_private` on PPC64LE: after p's check

In the working space of `Domain/Body.lean`, p in array 0, x's address and
length and y's address in the header's words 8–10: `cpCmp_split`, z (array
4) compared with 2, `p − 2` and y; `cpBody_ok`, x's range (`xRange`), then
status 2, or `z = g^x mod p` and its comparison (`cpGood`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.Derive
open VG.Impl.Ffdh.PPC64LE.CheckPrivate
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The registers `cpTail` writes. -/
def cpTailRegs : List Reg := zRegs ++ ([.r0, .r3, .r6, .r10, .r14, .r15, .r16, .r17, .r19, .r26, .r31] : List Reg)

/-- The condition for status 1: `z ∉ {0, 1, p − 1}` and `z = y`. -/
abbrev good (z p y : Nat) : Prop := (z ≠ 0 ∧ z ≠ 1 ∧ z ≠ p - 1) ∧ z = y

/-- `cpTail`: with z in array 4, p in array 0 and y's `k` octets at `r12`,
`r3 :=` 1 if `good`, else 0. -/
theorem cpTail_ok {s : State} {B Yv : Addr} {Z w k : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h23 : s.gpr .r23 = B) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (h12 : s.gpr .r12 = off Yv 0) (hw : 4 ≤ w) (hw' : w ≤ 128) (hZ : slot w 28 ≤ Z) (hk : 1 ≤ k)
    (hkw : k ≤ 8 * w) (hrdY : ∀ i < k, InRegions (s.rd ++ s.wr) (off Yv i) 1)
    (hsepY : ∀ i < k, ∀ x, ofs B x < Z → off Yv i ≠ x) (hp : 1 ≤ arr s.mem B w 0) :
    WP isa cpTail s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if good (arr s.mem B w 4) (arr s.mem B w 0)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k)) then 1 else 0) ∧
        Body B w s.mem t.mem ∧ t.gpr .r23 = B) ∧ Keep cpTailRegs s t := by
  have hnw := hs.nowrap
  obtain e0 := Domain.slot_eq w 0; have e4 := Domain.slot_eq w 4; have e5 := Domain.slot_eq w 5
  obtain e8 := Domain.slot_eq w 8; have e9 := Domain.slot_eq w 9; have e28 := Domain.slot_eq w 28
  generalize hz : arr s.mem B w 4 = z
  generalize hP : arr s.mem B w 0 = p at hp
  generalize hy : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k) = y
  unfold cpTail
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = B ∧ t.mem = s.mem) (by
      prun [h23, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a31, m1⟩, k1⟩ => ?_)
  obtain e1 : Env s₁ B Z w := ⟨hs.congr k1.wr, (k1.gpr .r10 (by decide)).trans h10,
    (k1.gpr .r29 (by decide)).trans h29, (k1.gpr .r11 (by decide)).trans h11, a31, hw, hw', hZ⟩
  refine WP.seq (WP.mono (zMask_ok e1 ((k1.gpr .r23 (by decide)).trans h23) (by rw [m1, hP]; exact hp))
    fun s₂ ⟨⟨a26, z2, p2, o2, a10⟩, k2⟩ => ?_)
  rw [m1, hz, hP] at a26
  rw [m1, hz] at z2
  rw [m1, hP] at p2
  rw [m1] at o2
  obtain k12 := k1.trans k2
  obtain b2 : Body B w s.mem s₂.mem := Body.of o2 (by omega_using [e0, e5]) (by omega_using [e5, e28])
  unfold loadY
  refine WP.seq ?_
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain e2 : Env s₂ B Z w := ⟨hs.congr k12.wr, a10, (k12.gpr .r29 (by decide)).trans h29,
    (k12.gpr .r11 (by decide)).trans h11, (k2.gpr .r31 (by decide)).trans a31, hw, hw', hZ⟩
  refine WP.mono (e2.base (rd := .r10) (by decide) (by decide) 8) fun s₃ ⟨⟨a10₃, m3⟩, k3⟩ => ?_
  refine WP.mono (WP.keep [.r6] (Q := fun t => t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s₃.mem) (by
      prun [(k3.gpr .r28 (by decide)).trans ((k12.gpr .r28 (by decide)).trans h28), BitVec.add_zero])
    (by decide)) fun s₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  obtain k14 := (k12.trans k3).trans k4
  refine WP.seq (WP.mono (loadN_ok (dA := slot w 8) (hs.congr k14.wr) ((k4.gpr .r10 (by decide)).trans a10₃)
    ((k14.gpr .r12 (by decide)).trans h12) a6 ((k14.gpr .r11 (by decide)).trans h11) hk hkw (by omega_using [hw'])
    (by omega_using [e8]) (by omega_using [hZ, e8, e28]) (by rw [k14.rd, k14.wr]; exact hrdY) hsepY) fun s₅ ⟨v8, o5, k5⟩ => ?_)
  rw [m4, m3, b2.bytesAt hZ hsepY, hy] at v8
  obtain k15 := k14.trans k5
  have hh : hdrBytes = 256 := rfl
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₅.mem) (by
      prun [(k15.gpr .r23 (by decide)).trans h23, hh, BitVec.add_zero]
      simp [off, slot, hh]) (by decide)) fun s₆ ⟨⟨a10₆, m6⟩, k6⟩ => ?_
  obtain k16 := k15.trans k6
  obtain e6 : Env s₆ B Z w := ⟨hs.congr k16.wr, a10₆, (k16.gpr .r29 (by decide)).trans h29,
    (k16.gpr .r11 (by decide)).trans h11, ((k3.trans k4).trans (k5.trans k6)).gpr .r31 (by decide) |>.trans
      ((k2.gpr .r31 (by decide)).trans a31), hw, hw', hZ⟩
  refine WP.seq (WP.mono (eqMask_ok e6 .r19 (a := 4) (b := 8) (by decide) (by decide)) fun s₇ ⟨⟨a19, m7⟩, k7⟩ => ?_)
  obtain o5' : Outside B (slot w 8) (8 * w) s₂.mem s₆.mem := by rw [m6, ← m3, ← m4]; exact o5
  obtain z6 : val32 s₆.mem B (slot w 4) (2 * w) = z := by rw [Outside.val32 o5' (by omega_using [e4, e8]) (by omega_using [hw', e4])]; exact z2
  obtain y6 : val32 s₆.mem B (slot w 8) (2 * w) = y := by rw [m6]; exact v8
  rw [z6, y6] at a19
  obtain k17 := k16.trans k7
  refine WP.mono (WP.keep [.r26, .r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (if good z p y then 1 else 0) ∧
      t.mem = s₇.mem) (by
      unfold both
      prun [(k7.gpr .r26 (by decide)).trans ((((k3.trans k4).trans (k5.trans k6)).gpr .r26 (by decide)).trans a26),
        a19, mask_and']
      rw [BitVec.and_comm, mask_and_one]
      congr 1
      by_cases h1 : z ≠ 0 ∧ z ≠ 1 ∧ z ≠ p - 1 <;> by_cases h2 : z = y <;> simp [good, h1, h2]) (by decide))
    fun t ⟨⟨t3, mt⟩, kt⟩ => ⟨⟨t3, ?_, (kt.gpr .r23 (by decide)).trans ((k17.gpr .r23 (by decide)).trans h23)⟩,
      (k17.trans kt).mono (by decide)⟩
  rw [mt, m7]
  exact Outside.trans b2 (Body.of o5' (by omega_using [e0, e8]) (by omega_using [e8, e28]))

/-- `cpCmp`, split after y's address is loaded from the header's word 10. -/
theorem cpCmp_split {s : State} {B Yv : Addr} {Z w k : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h23 : s.gpr .r23 = B) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (hY : s.mem.readW (off B 80) 64 = off Yv 0) (hw : 4 ≤ w) (hw' : w ≤ 128) (hZ : slot w 28 ≤ Z) (hk : 1 ≤ k)
    (hkw : k ≤ 8 * w) (hrdY : ∀ i < k, InRegions (s.rd ++ s.wr) (off Yv i) 1)
    (hsepY : ∀ i < k, ∀ x, ofs B x < Z → off Yv i ≠ x) (hp : 1 ≤ arr s.mem B w 0) :
    WP isa (.block [.load .d .r12 .r23 80]) s fun s₁ =>
      (s₁.gpr .r12 = off Yv 0 ∧ s₁.gpr .r10 = off B (slot w 0) ∧ s₁.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧
        s₁.gpr .r23 = B ∧ s₁.gpr .r28 = BitVec.ofNat 64 k ∧ s₁.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) ∧
      WP isa cpTail s₁ fun t =>
        (t.gpr .r3 = BitVec.ofNat 64 (if good (arr s.mem B w 4) (arr s.mem B w 0)
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k)) then 1 else 0) ∧
          Body B w s.mem t.mem ∧ t.gpr .r23 = B) ∧ Keep (([.r12] : List Reg) ++ cpTailRegs) s t := by
  have hnw := hs.nowrap
  obtain e28 := Domain.slot_eq w 28
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = off Yv 0 ∧ t.mem = s.mem) (by
      prun [h23, hs.ld (d := 80) (n := 8) (by omega_using [hZ, e28]), hY]) (by decide)) fun s₁ ⟨⟨a12, m1⟩, k1⟩ =>
    ⟨⟨a12, (k1.gpr .r10 (by decide)).trans h10, (k1.gpr .r11 (by decide)).trans h11,
      (k1.gpr .r23 (by decide)).trans h23, (k1.gpr .r28 (by decide)).trans h28,
      (k1.gpr .r29 (by decide)).trans h29⟩, ?_⟩
  refine WP.mono (cpTail_ok (Yv := Yv) (hs.congr k1.wr) ((k1.gpr .r10 (by decide)).trans h10)
    ((k1.gpr .r29 (by decide)).trans h29) ((k1.gpr .r11 (by decide)).trans h11) ((k1.gpr .r23 (by decide)).trans h23)
    ((k1.gpr .r28 (by decide)).trans h28) a12 hw hw' hZ hk hkw (by rw [k1.rd, k1.wr]; exact hrdY) hsepY
    (by rw [m1]; exact hp)) fun t ⟨⟨t3, tb, t23⟩, kt⟩ => ⟨⟨?_, by rw [← m1]; exact tb, t23⟩, k1.trans kt⟩
  rw [t3, m1]

/-- The registers `cpBody` writes. -/
def cpBodyRegs : List Reg :=
  xRangeRegs ++ exPowRegs ++ ([.r3, .r9, .r12] : List Reg) ++ cpTailRegs

/-- `cpBody`: 2 if x is out of range; else 1 if `z = g^x mod p` (g's `k`
octets at `D + k`) is `good` with y, else 0. -/
theorem cpBody_ok {s : State} {B D X Yv : Addr} {Z w k L xl p x g y b : Nat} (h : Env s B Z w)
    (h23 : s.gpr .r23 = B) (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hwk : w = (k + 7) / 8) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hL : L = 2 * k ∨ L = 3 * k) (hxl : 1 ≤ xl) (hxk : xl ≤ k)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hXL : s.mem.readW (off B 72) 64 = BitVec.ofNat 64 xl)
    (hY : s.mem.readW (off B 80) 64 = off Yv 0)
    (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) (hsepD : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (hrdX : ∀ i < xl, InRegions (s.rd ++ s.wr) (off X i) 1) (hsepX : ∀ i < xl, ∀ x, ofs B x < Z → off X i ≠ x)
    (hrdY : ∀ i < k, InRegions (s.rd ++ s.wr) (off Yv i) 1) (hsepY : ∀ i < k, ∀ x, ofs B x < Z → off Yv i ≠ x)
    (hP : arr s.mem B w 0 = p) (hp2 : 2 ≤ p) (hodd : p % 2 = 1)
    (hpt : 2 ^ (64 * (w - 1)) < p)
    (hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) = x) (hg : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) = g)
    (hy : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k) = y) (hb : bnd s.mem D k L p = b) :
    WP isa cpBody s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if ¬ (0 < x ∧ x < b) then 2 else if good (g ^ x % p) p y then 1 else 0) ∧
        ∀ i < 18, word t.mem B (112 + 8 * i) = word s.mem B (112 + 8 * i)) ∧ Keep cpBodyRegs s t := by
  have hs := h.hs
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  obtain e0 := Domain.slot_eq w 0; have e8 := Domain.slot_eq w 8; have e28 := Domain.slot_eq w 28
  obtain rdQ : L = 3 * k → ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1 := fun hq i hi => by
    rw [off_off']; exact hrdD _ (by omega_using [hq, hi])
  obtain sepQ : L = 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x := fun hq i hi => by
    rw [off_off']; exact hsepD _ (by omega_using [hq, hi])
  obtain rdG : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1 := fun i hi => by
    rw [off_off']; exact hrdD _ (by omega_using [hL, hi])
  obtain sepG : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x := fun i hi => by
    rw [off_off']; exact hsepD _ (by omega_using [hL, hi])
  unfold cpBody
  refine WP.seq (WP.mono (xRange_ok h h23 h21 h27 h28 (by omega_using [hk]) (by omega_using [hwk]) (by omega_using [hk', hL]) (by omega_using [hk']) hxl hxk hX hXL
    hrdX hsepX rdQ sepQ (by omega_using [hP, hp2])) fun s₁ ⟨⟨a26, p1, b1, a10⟩, k1⟩ => ?_)
  rw [hx, hP, hb] at a26
  rw [hP] at p1
  obtain e1 : Env s₁ B Z w := ⟨hs.congr k1.wr, a10, (k1.gpr .r29 (by decide)).trans h.h29,
    (k1.gpr .r11 (by decide)).trans h.h11, (k1.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  obtain hw1 : ∀ d, d + 8 ≤ 256 → word s₁.mem B d = word s.mem B d := fun d hd => by
    rw [Outside.word b1 (by omega_using [e0, hd]) (by omega_using [hd])]
  obtain g23 : s₁.gpr .r23 = B := (k1.gpr .r23 (by decide)).trans h23
  obtain g28 : s₁.gpr .r28 = BitVec.ofNat 64 k := (k1.gpr .r28 (by decide)).trans h28
  refine WP.ite (s₁.gpr .r26 == 0) (eval_zero _ _) (fun hv => ?_) (fun hv => ?_)
  · -- Out of range.
    rw [a26, mask_beq_zero, Bool.not_eq_true', decide_eq_false_iff_not] at hv
    refine WP.mono (li_ok s₁ 2 (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨?_, fun i hi => ?_⟩,
      (k1.trans kt).mono (by decide)⟩
    · rw [t3, ite_eq_left hv]
    · rw [tm, hw1 _ (by omega_using [hi])]
  · -- In range.
    rw [a26, mask_beq_zero, Bool.not_eq_false', decide_eq_true_eq] at hv
    unfold cpGood
    refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off D k ∧ t.mem = s₁.mem) (by
        prun [(k1.gpr .r21 (by decide)).trans h21, g28]) (by decide)) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_)
    obtain k12 := k1.trans k2
    obtain e2 := e1.keep k2 (by decide)
    obtain b12 : Body B w s.mem s₂.mem := by rw [m2]; exact b1
    refine WP.seq (WP.mono (exPower_ok (Y := off D k) (X := X) (k := k) (xl := xl) e2
      ((k2.gpr .r23 (by decide)).trans g23) a9 ((k2.gpr .r28 (by decide)).trans g28) (by omega_using [hk]) (by omega_using [hwk]) hxl
      (by omega_using [hk', hxk]) (by rw [k12.rd, k12.wr]; exact rdG) sepG (by rw [k12.rd, k12.wr]; exact hrdX) hsepX
      (by rw [m2]; exact (hw1 64 (by omega_using [])).trans hX) (by rw [m2]; exact (hw1 72 (by omega_using [])).trans hXL)
      (by rw [m2, p1]; exact hp2) (by rw [m2, p1]; exact hodd)
      (by rw [m2, p1]; exact hpt)) fun s₃ ⟨⟨z3, p3, b3, r10₃⟩, k3⟩ => ?_)
    rw [b12.bytesAt hZ sepG, b12.bytesAt hZ hsepX, hg, hx, m2, p1] at z3
    rw [m2, p1] at p3
    obtain k13 := k12.trans k3
    obtain b13 : Body B w s.mem s₃.mem := Outside.trans b12 b3
    unfold cpCmp
    refine WP.seq (WP.mono (cpCmp_split (Yv := Yv) (hs.congr k13.wr) r10₃ ((k13.gpr .r29 (by decide)).trans h.h29)
      ((k13.gpr .r11 (by decide)).trans h.h11) ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans g23))
      ((k3.gpr .r28 (by decide)).trans ((k2.gpr .r28 (by decide)).trans g28))
      (by show Mont.word s₃.mem B 80 = _; rw [Outside.word b13 (by omega_using [e0]) (by omega_using [])]; exact hY) hw hw' hZ
      (by omega_using [hk]) (by omega_using [hwk]) (by rw [k13.rd, k13.wr]; exact hrdY) hsepY (by rw [p3]; omega_using [hp2]))
      fun s₄ ⟨_, hw4⟩ => WP.mono hw4 fun t ⟨⟨t3, tb, _⟩, kt⟩ => ?_)
    rw [z3, p3, b13.bytesAt hZ hsepY, hy] at t3
    refine ⟨⟨?_, fun i hi => ?_⟩, (k13.trans kt).mono (by decide)⟩
    · rw [t3]; exact congrArg _ (ite_eq_right (fun h' => h' hv)).symm
    · rw [Outside.word tb (by omega_using [e0, hi]) (by omega_using [hi]), Outside.word b13 (by omega_using [e0, hi]) (by omega_using [hi])]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate

end

end

/-!
# FFDH's key pairs on PPC64LE: the status

For a valid domain of `L` octets at `D`, `privateStatus` of y and x as the
code computes it: 2 unless `0 < x < bnd`, else 1 if `g^x mod p` is `good`
with y (not 0, 1 or `p − 1`, and y), else 0 (`privateStatus_dom`): with
`y = g^x mod p`, y is valid exactly when `g^x mod p` is in `2..p − 2`
(`publicValid_power`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)
open VG.Proof.Mont (off)
open VG.Proof.Ffdh.PPC64LE.Derive (bnd)

/-- `privateStatus` for a valid domain of `L = 2 k` or `3 k` octets at `D`. -/
theorem privateStatus_dom {m : Mem} {D : Addr} {k L : Nat} (hk : 0 < k) (hL : L = 2 * k ∨ L = 3 * k)
    (hv : domainValid k (bytesAt m D L) = true) (y x : Nat) :
    privateStatus (domainOf k (bytesAt m D L)) y x =
      if ¬ (0 < x ∧ x < bnd m D k L (os2ip (bytesAt m D k))) then 2 else
        if good (os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k)) (os2ip (bytesAt m D k)) y then 1
        else 0 := by
  have hpv : parametersValid (domainOf k (bytesAt m D L)) = true := by
    unfold domainValid at hv
    simp only [Bool.and_eq_true] at hv
    exact hv.1
  have h2k : 2 * k ≤ L := by omega_using [hL]
  have hmod := Proof.Ffdh.domainValid_mod hv
  have hp2 : 2 ≤ (domainOf k (bytesAt m D L)).p := (Proof.Ffdh.PPC64LE.Domain.modulus_facts hmod).1
  rw [Proof.Ffdh.privateStatus_eq hpv, Proof.Ffdh.PPC64LE.Derive.privateValid_dom hk hL]
  by_cases h : 0 < x ∧ x < bnd m D k L (os2ip (bytesAt m D k))
  · simp only [h, and_self, decide_true, Bool.true_eq_false, ↓reduceIte, not_true_eq_false]
    have hc : (publicValid ⟨domainOf k (bytesAt m D L), y⟩ = true ∧
        (domainOf k (bytesAt m D L)).g ^ x % (domainOf k (bytesAt m D L)).p = y) ↔
        good (os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k)) (os2ip (bytesAt m D k)) y := by
      rw [← Proof.Ffdh.domainOf_p m D h2k, show os2ip (bytesAt m (off D k) k) = (domainOf k (bytesAt m D L)).g by
        rw [Proof.Ffdh.domainOf_g m D h2k]]
      have hz := Nat.mod_lt ((domainOf k (bytesAt m D L)).g ^ x) (show 0 < (domainOf k (bytesAt m D L)).p by omega_using [hp2])
      constructor
      · rintro ⟨hy, rfl⟩
        have := (Proof.Ffdh.publicValid_power hpv x).mp hy
        exact ⟨by omega_using [this], rfl⟩
      · rintro ⟨hr, rfl⟩
        exact ⟨(Proof.Ffdh.publicValid_power hpv x).mpr (by omega_using [hz, hr]), rfl⟩
    by_cases hg : good (os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k)) (os2ip (bytesAt m D k)) y
    · rw [ite_eq_left (hc.mpr hg), ite_eq_left hg]
    · rw [ite_eq_right (fun h' => hg (hc.mp h')), ite_eq_right hg]
  · simp [h]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate

end

end

/-!
# `vg_ffdh_check_private` on PPC64LE: the front

`cpFront` saves the nonvolatile registers in the working space's header,
stores x, `x_len` and y's address in its words 8–10 (`kpHdr_ok`), sets up
the registers and g's address in `r9`. It reaches `Base` for the domain of
`kdOf`, whose y is g, and `ExtK`: the header's words, x's and y's bytes,
readable and apart from the working space (`kp_front`), keeping the bytes
apart from the working space.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.CheckPrivate
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The public data of a run: the domain, g (as `CD`'s y) and the working
space; x's address and length, y's address, the bound on x and whether x is
within it. -/
structure KD where
  c : CD
  X : Addr
  xl : Nat
  Yv : Addr
  b : Nat
  v : Bool

/-- x's value in `s`. -/
abbrev xvalK (d : KD) (s : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.X d.xl)

def kdOf (s : State) : KD :=
  let c : CD := ⟨s.gpr .r3, off (s.gpr .r3) (s.gpr .r5).toNat, s.gpr .r10, (s.gpr .r5).toNat, (s.gpr .r4).toNat,
    (stackArg s 0).toNat * 8, Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat,
    Spec.Rsa.bytesAt s.mem (off (s.gpr .r3) (s.gpr .r5).toNat) (s.gpr .r5).toNat⟩
  let b := bnd s.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat c.p
  let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  ⟨c, s.gpr .r8, (s.gpr .r9).toNat, s.gpr .r6, b, decide (0 < x ∧ x < b)⟩

/-- What holds of x and y from the header's stores on. -/
structure ExtK (d : KD) (s : State) : Prop where
  wX : s.mem.readW (off d.c.S 64) 64 = off d.X 0
  wXL : s.mem.readW (off d.c.S 72) 64 = BitVec.ofNat 64 d.xl
  wY : s.mem.readW (off d.c.S 80) 64 = off d.Yv 0
  rdX : ∀ i < d.xl, InRegions (s.rd ++ s.wr) (off d.X i) 1
  sepX : ∀ i < d.xl, ∀ y, ofs d.c.S y < d.c.Z → off d.X i ≠ y
  rdY : ∀ i < d.c.k, InRegions (s.rd ++ s.wr) (off d.Yv i) 1
  sepY : ∀ i < d.c.k, ∀ y, ofs d.c.S y < d.c.Z → off d.Yv i ≠ y
  xl1 : 1 ≤ d.xl
  xlk : d.xl ≤ d.c.k

theorem ExtK.keep {d : KD} {s t : State} {rs : List Reg} (h : ExtK d s) (k : Keep rs s t)
    (hm : Body d.c.S d.c.w s.mem t.mem) : ExtK d t where
  wX := by
    have := Domain.slot_eq d.c.w 0
    show word t.mem d.c.S 64 = _
    rw [Outside.word hm (Or.inl (by omega_using [this])) (by omega_using [])]; exact h.wX
  wXL := by
    have := Domain.slot_eq d.c.w 0
    show word t.mem d.c.S 72 = _
    rw [Outside.word hm (Or.inl (by omega_using [this])) (by omega_using [])]; exact h.wXL
  wY := by
    have := Domain.slot_eq d.c.w 0
    show word t.mem d.c.S 80 = _
    rw [Outside.word hm (Or.inl (by omega_using [this])) (by omega_using [])]; exact h.wY
  rdX := by rw [k.rd, k.wr]; exact h.rdX
  sepX := h.sepX
  rdY := by rw [k.rd, k.wr]; exact h.rdY
  sepY := h.sepY
  xl1 := h.xl1
  xlk := h.xlk

/-- The registers `cpFront` writes. -/
def kpFrontRegs : List Reg := ([.r23] : List Reg) ++ setup0Regs ++ ([.r9] : List Reg)

/-- x, `x_len` and y's address into the header's words 8–10 at `S`. -/
theorem kpHdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S)
    (hin : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8) :
    WP isa (.block ([.store .d .r8 .r23 64, .store .d .r9 .r23 72, .store .d .r6 .r23 80] : List Instr)) s fun t =>
      (word t.mem S 64 = s.gpr .r8 ∧ word t.mem S 72 = s.gpr .r9 ∧ word t.mem S 80 = s.gpr .r6 ∧
        Outside S 64 24 s.mem t.mem) ∧ Keep [] s t := by
  refine WP.keep _ ?_ (by decide)
  obtain i0 : InRegions s.wr (S + BitVec.ofNat 64 64) 8 := hin 0 (by decide)
  obtain i1 : InRegions s.wr (S + BitVec.ofNat 64 72) 8 := hin 1 (by decide)
  obtain i2 : InRegions s.wr (S + BitVec.ofNat 64 80) 8 := hin 2 (by decide)
  prun [h23, i0, i1, i2, BitVec.add_zero]
  obtain o0 := writeW_outside s.mem S (d := 64) (s.gpr .r8) (by omega_using [])
  obtain o1 := writeW_outside (s.mem.writeW (off S 64) (s.gpr .r8)) S (d := 72) (s.gpr .r9) (by omega_using [])
  obtain o2 := writeW_outside ((s.mem.writeW (off S 64) (s.gpr .r8)).writeW (off S 72) (s.gpr .r9)) S (d := 80)
    (s.gpr .r6) (by omega_using [])
  refine ⟨?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 64 = _
    rw [o2.word (by omega_using []) (by omega_using []), o1.word (by omega_using []) (by omega_using [])]
    exact word_writeW_self _ _ _ _
  · show word _ S 72 = _
    rw [o2.word (by omega_using []) (by omega_using [])]
    exact word_writeW_self _ _ _ _
  · exact ((o0.mono (by omega_using []) (by omega_using [])).trans (o1.mono (by omega_using []) (by omega_using []))).trans
      (o2.mono (by omega_using []) (by omega_using []))

/-- `cpFront`: `Base` and `ExtK` for `kdOf`, the saved registers in the
header, the bytes apart from the working space, and the registers it
writes. -/
theorem kp_front {s : State} (h : kpContract.pre s) :
    WP isa (.block cpFront) s fun t => Base (kdOf s).c t ∧ ExtK (kdOf s) t ∧
      (∀ i < 18, word t.mem (s.gpr .r10) (112 + 8 * i) = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)) ∧
      (∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (s.gpr .r10) y < (stackArg s 0).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n) ∧
      Keep kpFrontRegs s t := by
  obtain ⟨hsp, hrd, hwr, dDS, dYS, dXS, dSA, nwD, nwY, nwX, nwS, ⟨hk, hk'⟩, hL, hyl, hx1, hxk, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [kdOf]
  rw [hyl] at hrd dYS nwY
  generalize hDd : s.gpr .r3 = D at hrd dDS nwD ⊢
  generalize hLd : (s.gpr .r4).toNat = L at hrd dDS nwD hL ⊢
  generalize hkd : (s.gpr .r5).toNat = k at hk hk' hL hxk hsl hrd dYS nwY ⊢
  generalize hYd : s.gpr .r6 = Yv at hrd dYS nwY ⊢
  generalize hXd : s.gpr .r8 = X at hrd dXS nwX ⊢
  generalize hxd : (s.gpr .r9).toNat = xl at hrd dXS nwX hx1 hxk ⊢
  generalize hSd : s.gpr .r10 = S at hwr dDS dYS dXS dSA nwS ⊢
  generalize hZd : (stackArg s 0).toNat * 8 = Z at hwr dDS dYS dXS dSA nwS ⊢
  obtain hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_using [hL]
  obtain hZ256 : 256 ≤ Z := by omega_using [hsl, hZd]
  obtain hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [Domain.slot_eq]; omega_using [hsl, hZd, hk', hk]
  obtain hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  obtain hin : ∀ i < 18, InRegions s.wr (off (Domain.savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega_using [hZ256, hi]) (by omega_using [hi])⟩
  obtain hinH : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega_using [hZ256, hi]) (by omega_using [hi])⟩
  unfold cpFront
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Domain.save_ok (ws := .r10) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  obtain h23₁ : s₁.gpr .r23 = S := hS.r23.trans hSd
  obtain hfr₁ : Frame [Domain.savR S] s.mem s₁.mem := hSd ▸ hS.frame
  rw [WP.block_append_iff]
  refine WP.mono (kpHdr_ok h23₁ (by rw [k1.wr]; exact hinH)) fun s₂ ⟨⟨w8, w9, w10, o2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) ((k12.gpr .r3 (by decide)).trans hDd)
    (by rw [k12.gpr .r4 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [k12.gpr .r5 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k2.gpr .r23 (by decide)).trans h23₁) hk') fun s₃ ⟨⟨a21, a27, a28, a11', a29, a10, a31, m3⟩, k3⟩ => ?_
  obtain k123 := k12.trans k3
  refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off D k ∧ t.mem = s₃.mem) (by prun [a21, a28])
    (by decide)) fun t ⟨⟨a9, mt⟩, kt⟩ => ?_
  obtain kall := k123.trans kt
  obtain hb3 : ∀ (Q : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep => by
    rw [mt, m3, outside_bytesAt o2 (by omega_using [hZ256]) hsep]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hfr₁ _ fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    obtain hc' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega_using [hZ256])) _ hc
    exact hsep i (List.mem_range.mp hi) _ (by simp only [Region.Contains] at hc'; exact hc') rfl
  obtain sepD := sep_of_disjoint dDS (by omega_using [hLd])
  obtain rdD : ∀ i < L, InRegions (t.rd ++ t.wr) (off D i) 1 := fun i hi => by
    rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega_using [hLd]) i hi
  obtain sepG : ∀ i < k, ∀ x, ofs S x < Z → off (off D k) i ≠ x := fun i hi => by
    rw [off_off']; exact sepD _ (by omega_using [hLk, hi])
  obtain hw3 : ∀ d, word t.mem S d = word s₂.mem S d := fun d => by rw [mt, m3]
  refine ⟨⟨⟨hs.congr kall.wr, (kt.gpr .r10 (by decide)).trans a10, (kt.gpr .r29 (by decide)).trans a29,
    (kt.gpr .r11 (by decide)).trans a11', (kt.gpr .r31 (by decide)).trans a31, show 4 ≤ (k + 7) / 8 by omega_using [hk],
    show (k + 7) / 8 ≤ 128 by omega_using [hk'], hZw⟩, (kt.gpr .r21 (by decide)).trans a21,
    (kt.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans h23₁)),
    (kt.gpr .r27 (by decide)).trans a27, (kt.gpr .r28 (by decide)).trans a28,
    hk, hk', by simp only [Spec.Ffdh.domainLenValid] at hL; omega, rdD, sepD,
    fun i (hi : i < k) => by rw [off_off']; exact rdD _ (by omega_using [hLk, hi]), sepG, hb3 D L sepD, hb3 (off D k) k sepG⟩,
    ⟨?_, ?_, ?_,
    fun i hi => by rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := X) (L := xl) (by rw [hrd]; simp) (by omega_using [hxd]) i hi,
    sep_of_disjoint (L := xl) dXS (by omega_using [hxd]),
    fun i hi => by rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := Yv) (L := k) (by rw [hrd]; simp) (by omega_using [hkd]) i hi,
    sep_of_disjoint (L := k) dYS (by omega_using [hkd]), hx1, hxk⟩, fun i hi => ?_, hb3, kall.mono (by decide)⟩
  · show word t.mem S 64 = _
    rw [hw3, w8, k1.gpr .r8 (by decide), hXd]; simp [off]
  · show word t.mem S 72 = _
    rw [hw3, w9, k1.gpr .r9 (by decide), ← hxd, VG.Proof.Bignum.ofNat_toNat64]
  · show word t.mem S 80 = _
    rw [hw3, w10, k1.gpr .r6 (by decide), hYd]; simp [off]
  · rw [hw3, o2.word (by omega_using []) (by omega_using [hi])]
    obtain ea : off (Domain.savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← hS.saved i hi, hSd, ea]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
