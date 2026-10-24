module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

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
  have e0 := Domain.slot_eq w 0; have e4 := Domain.slot_eq w 4; have e5 := Domain.slot_eq w 5
  have e8 := Domain.slot_eq w 8; have e9 := Domain.slot_eq w 9; have e28 := Domain.slot_eq w 28
  generalize hz : arr s.mem B w 4 = z
  generalize hP : arr s.mem B w 0 = p at hp
  generalize hy : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k) = y
  unfold cpTail
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = B ∧ t.mem = s.mem) (by
      prun [h23, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a31, m1⟩, k1⟩ => ?_)
  have e1 : Env s₁ B Z w := ⟨hs.congr k1.wr, (k1.gpr .r10 (by decide)).trans h10,
    (k1.gpr .r29 (by decide)).trans h29, (k1.gpr .r11 (by decide)).trans h11, a31, hw, hw', hZ⟩
  refine WP.seq (WP.mono (zMask_ok e1 ((k1.gpr .r23 (by decide)).trans h23) (by rw [m1, hP]; exact hp))
    fun s₂ ⟨⟨a26, z2, p2, o2, a10⟩, k2⟩ => ?_)
  rw [m1, hz, hP] at a26
  rw [m1, hz] at z2
  rw [m1, hP] at p2
  rw [m1] at o2
  have k12 := k1.trans k2
  have b2 : Body B w s.mem s₂.mem := Body.of o2 (by omega) (by omega)
  unfold loadY
  refine WP.seq ?_
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have e2 : Env s₂ B Z w := ⟨hs.congr k12.wr, a10, (k12.gpr .r29 (by decide)).trans h29,
    (k12.gpr .r11 (by decide)).trans h11, (k2.gpr .r31 (by decide)).trans a31, hw, hw', hZ⟩
  refine WP.mono (e2.base (rd := .r10) (by decide) (by decide) 8) fun s₃ ⟨⟨a10₃, m3⟩, k3⟩ => ?_
  refine WP.mono (WP.keep [.r6] (Q := fun t => t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s₃.mem) (by
      prun [(k3.gpr .r28 (by decide)).trans ((k12.gpr .r28 (by decide)).trans h28), BitVec.add_zero])
    (by decide)) fun s₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  have k14 := (k12.trans k3).trans k4
  refine WP.seq (WP.mono (loadN_ok (dA := slot w 8) (hs.congr k14.wr) ((k4.gpr .r10 (by decide)).trans a10₃)
    ((k14.gpr .r12 (by decide)).trans h12) a6 ((k14.gpr .r11 (by decide)).trans h11) hk hkw (by omega)
    (by omega) (by omega) (by rw [k14.rd, k14.wr]; exact hrdY) hsepY) fun s₅ ⟨v8, o5, k5⟩ => ?_)
  rw [m4, m3, b2.bytesAt hZ hsepY, hy] at v8
  have k15 := k14.trans k5
  have hh : hdrBytes = 256 := rfl
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₅.mem) (by
      prun [(k15.gpr .r23 (by decide)).trans h23, hh, BitVec.add_zero]
      simp [off, slot, hh]) (by decide)) fun s₆ ⟨⟨a10₆, m6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  have e6 : Env s₆ B Z w := ⟨hs.congr k16.wr, a10₆, (k16.gpr .r29 (by decide)).trans h29,
    (k16.gpr .r11 (by decide)).trans h11, ((k3.trans k4).trans (k5.trans k6)).gpr .r31 (by decide) |>.trans
      ((k2.gpr .r31 (by decide)).trans a31), hw, hw', hZ⟩
  refine WP.seq (WP.mono (eqMask_ok e6 .r19 (a := 4) (b := 8) (by decide) (by decide)) fun s₇ ⟨⟨a19, m7⟩, k7⟩ => ?_)
  have o5' : Outside B (slot w 8) (8 * w) s₂.mem s₆.mem := by rw [m6, ← m3, ← m4]; exact o5
  have z6 : val32 s₆.mem B (slot w 4) (2 * w) = z := by rw [Outside.val32 o5' (by omega) (by omega)]; exact z2
  have y6 : val32 s₆.mem B (slot w 8) (2 * w) = y := by rw [m6]; exact v8
  rw [z6, y6] at a19
  have k17 := k16.trans k7
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
  exact Outside.trans b2 (Body.of o5' (by omega) (by omega))

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
  have e28 := Domain.slot_eq w 28
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = off Yv 0 ∧ t.mem = s.mem) (by
      prun [h23, hs.ld (d := 80) (n := 8) (by omega), hY]) (by decide)) fun s₁ ⟨⟨a12, m1⟩, k1⟩ =>
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
    (hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) = x) (hg : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) = g)
    (hy : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k) = y) (hb : bnd s.mem D k L p = b) :
    WP isa cpBody s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if ¬ (0 < x ∧ x < b) then 2 else if good (g ^ x % p) p y then 1 else 0) ∧
        ∀ i < 18, word t.mem B (112 + 8 * i) = word s.mem B (112 + 8 * i)) ∧ Keep cpBodyRegs s t := by
  have hs := h.hs
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := Domain.slot_eq w 0; have e8 := Domain.slot_eq w 8; have e28 := Domain.slot_eq w 28
  have rdQ : L = 3 * k → ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1 := fun hq i hi => by
    rw [off_off']; exact hrdD _ (by omega)
  have sepQ : L = 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x := fun hq i hi => by
    rw [off_off']; exact hsepD _ (by omega)
  have rdG : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1 := fun i hi => by
    rw [off_off']; exact hrdD _ (by omega)
  have sepG : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x := fun i hi => by
    rw [off_off']; exact hsepD _ (by omega)
  unfold cpBody
  refine WP.seq (WP.mono (xRange_ok h h23 h21 h27 h28 (by omega) (by omega) (by omega) (by omega) hxl hxk hX hXL
    hrdX hsepX rdQ sepQ (by omega)) fun s₁ ⟨⟨a26, p1, b1, a10⟩, k1⟩ => ?_)
  rw [hx, hP, hb] at a26
  rw [hP] at p1
  have e1 : Env s₁ B Z w := ⟨hs.congr k1.wr, a10, (k1.gpr .r29 (by decide)).trans h.h29,
    (k1.gpr .r11 (by decide)).trans h.h11, (k1.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  have hw1 : ∀ d, d + 8 ≤ 256 → word s₁.mem B d = word s.mem B d := fun d hd => by
    rw [Outside.word b1 (by omega) (by omega)]
  have g23 : s₁.gpr .r23 = B := (k1.gpr .r23 (by decide)).trans h23
  have g28 : s₁.gpr .r28 = BitVec.ofNat 64 k := (k1.gpr .r28 (by decide)).trans h28
  refine WP.ite (s₁.gpr .r26 == 0) (eval_zero _ _) (fun hv => ?_) (fun hv => ?_)
  · -- Out of range.
    rw [a26, mask_beq_zero, Bool.not_eq_true', decide_eq_false_iff_not] at hv
    refine WP.mono (li_ok s₁ 2 (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨?_, fun i hi => ?_⟩,
      (k1.trans kt).mono (by decide)⟩
    · rw [t3, ite_eq_left hv]
    · rw [tm, hw1 _ (by omega)]
  · -- In range.
    rw [a26, mask_beq_zero, Bool.not_eq_false', decide_eq_true_eq] at hv
    unfold cpGood
    refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off D k ∧ t.mem = s₁.mem) (by
        prun [(k1.gpr .r21 (by decide)).trans h21, g28]) (by decide)) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_)
    have k12 := k1.trans k2
    have e2 := e1.keep k2 (by decide)
    have b12 : Body B w s.mem s₂.mem := by rw [m2]; exact b1
    refine WP.seq (WP.mono (exPower_ok (Y := off D k) (X := X) (k := k) (xl := xl) e2
      ((k2.gpr .r23 (by decide)).trans g23) a9 ((k2.gpr .r28 (by decide)).trans g28) (by omega) (by omega) hxl
      (by omega) (by rw [k12.rd, k12.wr]; exact rdG) sepG (by rw [k12.rd, k12.wr]; exact hrdX) hsepX
      (by rw [m2]; exact (hw1 64 (by omega)).trans hX) (by rw [m2]; exact (hw1 72 (by omega)).trans hXL)
      (by rw [m2, p1]; exact hp2) (by rw [m2, p1]; exact hodd)) fun s₃ ⟨⟨z3, p3, b3, r10₃⟩, k3⟩ => ?_)
    rw [b12.bytesAt hZ sepG, b12.bytesAt hZ hsepX, hg, hx, m2, p1] at z3
    rw [m2, p1] at p3
    have k13 := k12.trans k3
    have b13 : Body B w s.mem s₃.mem := Outside.trans b12 b3
    unfold cpCmp
    refine WP.seq (WP.mono (cpCmp_split (Yv := Yv) (hs.congr k13.wr) r10₃ ((k13.gpr .r29 (by decide)).trans h.h29)
      ((k13.gpr .r11 (by decide)).trans h.h11) ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans g23))
      ((k3.gpr .r28 (by decide)).trans ((k2.gpr .r28 (by decide)).trans g28))
      (by show Mont.word s₃.mem B 80 = _; rw [Outside.word b13 (by omega) (by omega)]; exact hY) hw hw' hZ
      (by omega) (by omega) (by rw [k13.rd, k13.wr]; exact hrdY) hsepY (by rw [p3]; omega))
      fun s₄ ⟨_, hw4⟩ => WP.mono hw4 fun t ⟨⟨t3, tb, _⟩, kt⟩ => ?_)
    rw [z3, p3, b13.bytesAt hZ hsepY, hy] at t3
    refine ⟨⟨?_, fun i hi => ?_⟩, (k13.trans kt).mono (by decide)⟩
    · rw [t3]; exact congrArg _ (ite_eq_right (fun h' => h' hv)).symm
    · rw [Outside.word tb (by omega) (by omega), Outside.word b13 (by omega) (by omega)]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
