module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Domain
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# FFDH's domain operations on PPC64LE: loading p and the range of y

In the working space at `B` (`Env`, as the Miller–Rabin round's: array 0 at
`r10`, the arrays' size in `r29`, `2 w` in `r11`, `B` in `r31`), whose
arrays change only from array 0 on (`Body`):

* `loadP_ok`: p's `k` octets into array 0, and `r0 = 0` exactly when it is a
  valid modulus;
* `range_ok`: y's `k` octets into array 4, and `r26` the mask of
  `1 < y < p − 1`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot slot_sep bytesAt_length)

/-- Memory that changed only in the 28 arrays. -/
abbrev Body (B : Addr) (w : Nat) (m m' : Mem) : Prop := Outside B (slot w 0) (28 * (8 * (w + 2))) m m'

theorem slot28 (w : Nat) : slot w 28 = slot w 0 + 28 * (8 * (w + 2)) := by
  simp only [slot]; omega

theorem Body.of {B : Addr} {w o n : Nat} {m m' : Mem} (h : Outside B o n m m') (ho : slot w 0 ≤ o)
    (hn : o + n ≤ slot w 28) : Body B w m m' :=
  h.mono ho (by rw [slot28] at hn; omega)

/-- `loadP`: p's `k` octets at `D` (`r21`, `k` in `r28`) into array 0, and
`r0 = 0` exactly when p is a valid modulus. -/
theorem loadP_ok {s : State} {B D : Addr} {Z w k : Nat} (h : Env s B Z w) (h21 : s.gpr .r21 = D)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hwk : w = (k + 7) / 8) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa loadP s fun t =>
      (arr t.mem B w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) ∧
        (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k)) k = true) ∧
        Body B w s.mem t.mem) ∧ Keep [.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have h28Z := slot_lt (w := w) (show 0 < 28 by decide)
  unfold loadP
  have hpre : WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s fun t =>
      (t.gpr .r12 = off D 0 ∧ t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s.mem) ∧ Keep [.r6, .r12] s t := by
    refine WP.keep _ ?_ (by decide)
    prun [h21, h28, BitVec.add_zero]
  refine WP.seq (WP.mono hpre fun s₀ ⟨⟨a12, a6, m0⟩, k0⟩ => ?_)
  have hs₀ := hs.congr k0.wr
  refine WP.seq (WP.mono (loadN_ok (dA := slot w 0) hs₀ ((k0.gpr .r10 (by decide)).trans h.h10) a12 a6
    ((k0.gpr .r11 (by decide)).trans h.h11) (by omega) (by omega) (by have := h.hw'; omega)
    (by simp only [slot, hdrBytes]; omega) (by omega) (by rw [k0.rd, k0.wr]; exact hrd) hsep)
    fun s₁ ⟨hv₁, out₁, k₁⟩ => ?_)
  have hN₁ : ∀ i < k, s₁.mem (off D i) = s.mem (off D i) := fun i hi => by
    rw [out₁ _ (Or.inr (by
      have := hsep i hi (off D i)
      simp only [ofs] at this ⊢
      by_contra hc; exact this (by omega) rfl)), m0]
  refine WP.mono (check_ok (N := D) (nb := Spec.Rsa.bytesAt s.mem D k)
    ((k₁.gpr .r12 (by decide)).trans a12) ((k₁.gpr .r6 (by decide)).trans a6) hk hk' (bytesAt_length _ _ _)
    (by rw [k₁.rd, k₁.wr, k0.rd, k0.wr]; exact hrd) fun i hi => by
      rw [hN₁ i hi]; simp [Spec.Rsa.bytesAt, off]) fun t ⟨hc, mt, kt⟩ => ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [arr, mt, hv₁, m0]
  · exact hc
  · rw [mt, ← m0]; exact Body.of out₁ (Nat.le_refl _) (by omega)
  · exact ((k0.trans k₁).trans kt).mono (by decide)

theorem slot_eq (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := rfl

/-- The registers `consts` writes. -/
def constsRegs : List Reg := [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20]

/-- `consts`: 1 into array 7, `p − 1` into array 6, 0 into array 5. -/
theorem consts_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (hp : 1 ≤ arr s.mem B w 0) :
    WP isa consts s fun t =>
      (arr t.mem B w 7 = 1 ∧ arr t.mem B w 6 = arr s.mem B w 0 - 1 ∧ arr t.mem B w 5 = 0 ∧
        Outside B (slot w 5) (3 * (8 * (w + 2))) s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
        Keep constsRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e5 := slot_eq w 5; have e6 := slot_eq w 6; have e7 := slot_eq w 7
  have e8 := slot_eq w 8; have e28 := slot_eq w 28
  unfold consts
  refine WP.seq (WP.mono (Pub.oneP_ok hs (by omega) (by omega) (by omega) h.h10 h.h29 h.h11)
    fun s₁ ⟨⟨v7, o1⟩, k1⟩ => ?_)
  have e1 := h.keep k1 (by decide)
  have p1 : arr s₁.mem B w 0 = arr s.mem B w 0 := Outside.val32 o1 (by omega) (by omega)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e1.base (rd := .r8) (by decide) (by decide) 0) fun s₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have e2 := e1.keep k2 (by decide)
  refine WP.mono (e2.base (rd := .r9) (by decide) (by decide) 6) fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have e3 := e2.keep k3 (by decide)
  refine WP.mono (e3.base (rd := .r10) (by decide) (by decide) 7) fun s₄ ⟨⟨a10, m4⟩, k4⟩ => ?_
  have k14 := ((k1.trans k2).trans k3).trans k4
  have hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  refine WP.seq (WP.mono (subMod_ok (dA := slot w 0) (dT := slot w 6) (dM := slot w 7) (n := 2 * w)
    (hs.congr k14.wr) ((k4.gpr .r8 (by decide)).trans ((k3.gpr .r8 (by decide)).trans a8))
    ((k4.gpr .r9 (by decide)).trans a9) a10 ((k14.gpr .r11 (by decide)).trans h.h11) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₅ ⟨⟨c, hc, hv, _⟩, o5, k5⟩ => ?_)
  rw [hm4] at hv
  have v6 : arr s₅.mem B w 6 = arr s.mem B w 0 - 1 := by
    have hT := val32_lt s₅.mem B (slot w 6) (2 * w)
    have hA := val32_lt s₁.mem B (slot w 0) (2 * w)
    simp only [arr] at v7 p1 hp ⊢
    rw [v7] at hv
    rw [p1] at hv hA
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
    · omega
    · rw [show 32 * (2 * w) = 64 * w by omega] at hT hv hA; omega
  have k15 := k14.trans k5
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hr10 : WP isa (.block [.addi .r10 .r23 hdrBytes]) s₅ fun t =>
      (t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₅.mem) ∧ Keep [.r10] s₅ t := by
    refine WP.keep _ ?_ (by decide)
    prun [(k15.gpr .r23 (by decide)).trans h23, hdrBytes]
    rw [show slot w 0 = 256 by simp [slot, hdrBytes]]
  refine WP.mono hr10 fun s₆ ⟨⟨a10', m6⟩, k6⟩ => ?_
  have e6' : Env s₆ B Z w := ⟨hs.congr (k15.trans k6).wr, a10',
    ((k15.trans k6).gpr .r29 (by decide)).trans h.h29, ((k15.trans k6).gpr .r11 (by decide)).trans h.h11,
    ((k15.trans k6).gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  refine WP.mono (e6'.base (rd := .r14) (by decide) (by decide) 5) fun s₇ ⟨⟨a14, m7⟩, k7⟩ => ?_
  refine WP.mono (zeroWords_ok (hs.congr ((k15.trans k6).trans k7).wr) a14
    ((k7.gpr .r11 (by decide)).trans e6'.h11) (by omega) (by omega) (by omega)) fun t ⟨⟨_, hz, o8⟩, k8⟩ => ?_
  have hm7 : s₇.mem = s₅.mem := by rw [m7, m6]
  refine ⟨⟨?_, ?_, ?_, ?_, (k8.gpr .r10 (by decide)).trans ((k7.gpr .r10 (by decide)).trans a10')⟩,
    (((k15.trans k6).trans k7).trans k8).mono (by decide)⟩
  · rw [arr, Outside.val32 o8 (by omega) (by omega), hm7, Outside.val32 o5 (by omega) (by omega), hm4]; exact v7
  · rw [arr, Outside.val32 o8 (by omega) (by omega), hm7]; exact v6
  · rw [arr, Pre.val32_eq_wv]
    exact (VG.Proof.Bignum.wv_eq_zero_iff _ _ _ _).mpr hz
  · refine Outside.trans (Outside.mono o1 (by omega) (by omega)) (Outside.trans (m₂ := s₅.mem) ?_ ?_)
    · rw [← hm4]; exact Outside.mono o5 (by omega) (by omega)
    · rw [← hm7]; exact Outside.mono o8 (by omega) (by omega)

theorem clear_mask (a b : Bool) : (mask a ||| mask b) ^^^ mask b = mask (a && !b) := by
  cases a <;> cases b <;> rfl

theorem mask_ite (p : Prop) [Decidable p] :
    BitVec.ofNat 64 0 - BitVec.ofNat 64 (if p then 1 else 0) = mask (decide p) := by
  by_cases h : p <;> simp [h, mask]

/-- The registers `range` writes. -/
def rangeRegs : List Reg :=
  [.r0, .r3, .r4, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r19, .r20, .r26]

/-- `r26 &= ¬r19` with masks. -/
theorem clear19_ok (s : State) {a b : Bool} (h26 : s.gpr .r26 = mask a) (h19 : s.gpr .r19 = mask b) :
    WP isa (.block clear19) s fun t => (t.gpr .r26 = mask (a && !b) ∧ t.mem = s.mem) ∧ Keep [.r26] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold clear19
  prun [h26, h19, clear_mask]

/-- `range`: y's `k` octets at `Y` (`r26`) into array 4, and `r26` the mask
of `1 < y < p − 1` for p in array 0. -/
theorem range_ok {s : State} {B Y : Addr} {Z w k : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h26 : s.gpr .r26 = Y) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off Y i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off Y i ≠ x) (hp : 1 ≤ arr s.mem B w 0) :
    WP isa range s fun t =>
      (arr t.mem B w 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) ∧ arr t.mem B w 0 = arr s.mem B w 0 ∧
        arr t.mem B w 7 = 1 ∧
        t.gpr .r26 = mask (decide (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) < arr s.mem B w 0 - 1)) ∧
        Body B w s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧ Keep rangeRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e3 := slot_eq w 3; have e4 := slot_eq w 4; have e5 := slot_eq w 5
  have e6 := slot_eq w 6; have e7 := slot_eq w 7; have e8 := slot_eq w 8; have e28 := slot_eq w 28
  generalize hy : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) = y
  generalize hP : arr s.mem B w 0 = p at hp
  unfold range
  have h9 : WP isa (.block [.addi .r9 .r26 0]) s fun t => (t.gpr .r9 = Y ∧ t.mem = s.mem) ∧ Keep [.r9] s t := by
    refine WP.keep _ ?_ (by decide)
    prun [h26, BitVec.add_zero]
  refine WP.seq (WP.mono h9 fun s₁ ⟨⟨a9, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (Pub.loadX_ok (hs.congr k1.wr) ((k1.gpr .r23 (by decide)).trans h23) a9
    ((k1.gpr .r28 (by decide)).trans h28) ((k1.gpr .r10 (by decide)).trans h.h10)
    ((k1.gpr .r29 (by decide)).trans h.h29) ((k1.gpr .r11 (by decide)).trans h.h11) hk hkw (by omega)
    (by omega) (by rw [k1.rd, k1.wr]; exact hrd) hsep) fun s₂ ⟨⟨v4, top4, o2, a10⟩, k2⟩ => ?_)
  rw [m1, hy] at v4
  have k12 := k1.trans k2
  have e2 : Env s₂ B Z w := ⟨hs.congr k12.wr, a10, (k12.gpr .r29 (by decide)).trans h.h29,
    (k12.gpr .r11 (by decide)).trans h.h11, (k12.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  have p2 : arr s₂.mem B w 0 = p := by rw [arr, Outside.val32 o2 (by omega) (by omega), m1]; exact hP
  refine WP.seq (WP.mono (consts_ok e2 ((k12.gpr .r23 (by decide)).trans h23) (by omega))
    fun s₃ ⟨⟨v7, v6, v5, o3, a10₃⟩, k3⟩ => ?_)
  rw [p2] at v6
  have k13 := k12.trans k3
  have p3 : arr s₃.mem B w 0 = p := by rw [arr, Outside.val32 o3 (by omega) (by omega)]; exact p2
  have y3 : arr s₃.mem B w 4 = y := by rw [arr, Outside.val32 o3 (by omega) (by omega)]; exact v4
  have t3 : word s₃.mem B (slot w 4 + 8 * w) = 0 := by
    rw [Outside.word o3 (by omega) (by omega)]; exact top4
  have e3' : Env s₃ B Z w := ⟨hs.congr k13.wr, a10₃, (k3.gpr .r29 (by decide)).trans e2.h29,
    (k3.gpr .r11 (by decide)).trans e2.h11, (k3.gpr .r31 (by decide)).trans e2.h31, hw, hw', hZ⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (e3'.base (rd := .r8) (by decide) (by decide) 4) fun s₄ ⟨⟨a8, m4⟩, k4⟩ => ?_
  refine WP.mono ((e3'.keep k4 (by decide)).base (rd := .r9) (by decide) (by decide) 3)
    fun s₅ ⟨⟨a9', m5⟩, k5⟩ => ?_
  have k35 := k4.trans k5
  have hm5 : s₅.mem = s₃.mem := by rw [m5, m4]
  refine WP.seq (WP.mono (subMod_ok (dA := slot w 4) (dT := slot w 3) (dM := slot w 0) (n := 2 * w)
    (hs.congr (k13.trans k35).wr) ((k5.gpr .r8 (by decide)).trans a8) a9' ((k35.gpr .r10 (by decide)).trans e3'.h10)
    ((k35.gpr .r11 (by decide)).trans e3'.h11) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun s₆ ⟨⟨c, hc, hv, h20⟩, o6, k6⟩ => ?_)
  rw [hm5] at hv h20
  have hw32 : w32 s₃.mem B (slot w 4 + 4 * (2 * w)) = 0 := by
    have := word_eq_w32 s₃.mem B (slot w 4 + 8 * w)
    rw [t3, show (0 : BitVec 64).toNat = 0 from rfl] at this
    rw [show slot w 4 + 4 * (2 * w) = slot w 4 + 8 * w by omega]; omega
  have hlt : (w32 s₃.mem B (slot w 4 + 4 * (2 * w)) < c) ↔ y < p := by
    have hT := val32_lt s₆.mem B (slot w 3) (2 * w)
    have hA := val32_lt s₃.mem B (slot w 4) (2 * w)
    have hM := val32_lt s₃.mem B (slot w 0) (2 * w)
    simp only [arr] at y3 p3
    rw [hw32]; rw [y3, p3] at hv; rw [y3] at hA; rw [p3] at hM
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
    · omega
    · rw [show 32 * (2 * w) = 64 * w by omega] at hT hv hA hM; omega
  rw [mask_ite] at h20
  simp only [hlt] at h20
  have k36 := (k13.trans k35).trans k6
  have e6' : Env s₆ B Z w := e3'.keep (k35.trans k6) (by decide)
  have o6' : Outside B (slot w 3) (8 * (w + 2)) s₃.mem s₆.mem := by
    rw [← hm5]; exact Outside.mono o6 (Nat.le_refl _) (by omega)
  have q6 : ∀ j, j < 28 → j ≠ 3 → arr s₆.mem B w j = arr s₃.mem B w j := fun j hj h3 =>
    Outside.arrEq o6' hj h3 (by omega)
  have h26' : WP isa (.block [.addi .r26 .r20 0]) s₆ fun t =>
      (t.gpr .r26 = mask (decide (y < p)) ∧ t.mem = s₆.mem) ∧ Keep [.r26] s₆ t := by
    refine WP.keep _ ?_ (by decide)
    prun [h20, BitVec.add_zero]
  refine WP.seq (WP.mono h26' fun s₇ ⟨⟨a26, m7⟩, k7⟩ => ?_)
  have e7' := e6'.keep k7 (by decide)
  have q7 : ∀ j, j < 28 → j ≠ 3 → arr s₇.mem B w j = arr s₃.mem B w j := fun j hj h3 => by
    rw [m7]; exact q6 j hj h3
  -- The three comparisons.
  refine WP.seq (WP.mono (eqMask_ok e7' .r19 (a := 4) (b := 5) (by decide) (by decide))
    fun s₈ ⟨⟨a19, m8⟩, k8⟩ => ?_)
  refine WP.seq (WP.mono (clear19_ok s₈ ((k8.gpr .r26 (by decide)).trans a26) a19) fun s₉ ⟨⟨b26, m9⟩, k9⟩ => ?_)
  have e9 := (e7'.keep k8 (by decide)).keep k9 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e9 .r19 (a := 4) (b := 7) (by decide) (by decide))
    fun s₁₀ ⟨⟨c19, m10⟩, k10⟩ => ?_)
  refine WP.seq (WP.mono (clear19_ok s₁₀ ((k10.gpr .r26 (by decide)).trans b26) c19)
    fun s₁₁ ⟨⟨c26, m11⟩, k11⟩ => ?_)
  have e11 := (e9.keep k10 (by decide)).keep k11 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e11 .r19 (a := 4) (b := 6) (by decide) (by decide))
    fun s₁₂ ⟨⟨d19, m12⟩, k12'⟩ => ?_)
  refine WP.mono (clear19_ok s₁₂ ((k12'.gpr .r26 (by decide)).trans c26) d19) fun t ⟨⟨d26, mt⟩, kt⟩ => ?_
  have hmt : t.mem = s₇.mem := by rw [mt, m12, m11, m10, m9, m8]
  have hm9 : s₉.mem = s₇.mem := by rw [m9, m8]
  have hm11 : s₁₁.mem = s₇.mem := by rw [m11, m10, hm9]
  have r4 : val32 s₇.mem B (slot w 4) (2 * w) = y := (q7 4 (by decide) (by decide)).trans y3
  have r5 : val32 s₇.mem B (slot w 5) (2 * w) = 0 := (q7 5 (by decide) (by decide)).trans v5
  have r6 : val32 s₇.mem B (slot w 6) (2 * w) = p - 1 := (q7 6 (by decide) (by decide)).trans v6
  have r7 : val32 s₇.mem B (slot w 7) (2 * w) = 1 := (q7 7 (by decide) (by decide)).trans v7
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hmt, q7 4 (by decide) (by decide)]; exact y3
  · rw [hmt, q7 0 (by decide) (by decide), p3]
  · rw [hmt, q7 7 (by decide) (by decide), v7]
  · rw [d26]
    simp only [hm9, hm11, r4, r5, r6, r7]
    congr 1
    simp only [Bool.and_assoc, Bool.decide_and]
    cases hb : decide (y < p) <;> cases h0 : decide (y = 0) <;> cases h1 : decide (y = 1) <;>
      cases h2 : decide (y = p - 1) <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb h0 h1 h2 <;>
      simp <;> omega
  · rw [hmt, m7]
    refine Outside.trans (m₂ := s₃.mem) ?_ (Outside.mono o6' (by omega) (by omega))
    refine Outside.trans (m₂ := s₂.mem) ?_ (Outside.mono o3 (by omega) (by omega))
    rw [← m1]; exact Outside.mono o2 (by omega) (by omega)
  · exact (((((((((k35.trans k6).trans k7).trans k8).trans k9).trans k10).trans k11).trans k12').trans kt).gpr
      .r10 (by decide)).trans a10₃
  · exact ((((((((((k13.trans k35).trans k6).trans k7).trans k8).trans k9).trans k10).trans k11).trans
      k12').trans kt).mono (by decide))

theorem Body.of_outs {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, slot w 0 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 28) : Body B w m m' := fun x hx =>
  h x fun r hr' => by have := hr r hr'; rw [slot28] at this; omega

theorem mask_and_one (b : Bool) : mask b &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (if b then 1 else 0) := by
  cases b <;> rfl

theorem two_pow_128 (w : Nat) : 2 ^ (128 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- The registers `subgroup` writes. -/
def subRegs : List Reg := ModExp.powSRegs ++ [.r0, .r3, .r4, .r5, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r20]

/-- `subgroup`: `r3 := 1` if `y^q mod p = 1` (y in array 4, p in array 0,
q's `k` octets at `D + 2 k`), else 0. -/
theorem subgroup_ok {s : State} {B D : Addr} {Z w k : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k ≤ 1024)
    (hp2 : 2 ≤ arr s.mem B w 0) (hodd : arr s.mem B w 0 % 2 = 1)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x) :
    WP isa subgroup s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if arr s.mem B w 4 ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) %
          arr s.mem B w 0 = 1 then 1 else 0) ∧ Body B w s.mem t.mem) ∧ Keep subRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e1 := slot_eq w 1; have e2 := slot_eq w 2; have e3 := slot_eq w 3
  have e4 := slot_eq w 4; have e5 := slot_eq w 5; have e6 := slot_eq w 6; have e7 := slot_eq w 7
  have e8 := slot_eq w 8; have e28 := slot_eq w 28
  generalize hP : arr s.mem B w 0 = p at hp2 hodd
  generalize hY : arr s.mem B w 4 = y
  generalize hQ : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) = q
  unfold subgroup
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .r5) (by decide) (by decide) 1) fun s₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  have e1' := h.keep k1 (by decide)
  refine WP.mono (e1'.base (rd := .r8) (by decide) (by decide) 2) fun s₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have e2' := e1'.keep k2 (by decide)
  refine WP.mono (e2'.base (rd := .r9) (by decide) (by decide) 3) fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have e3' := e2'.keep k3 (by decide)
  have hm3 : s₃.mem = s.mem := by rw [m3, m2, m1]
  have p3 : val32 s₃.mem B (slot w 0) (2 * w) = p := by rw [hm3]; exact hP
  refine WP.seq (WP.mono (r2_ok e3'.hs ((k3.gpr .r8 (by decide)).trans a8) a9 e3'.h10
    ((k3.gpr .r5 (by decide)).trans ((k2.gpr .r5 (by decide)).trans a5)) e3'.h11 (by omega) (by omega)
    (by omega) (by rw [p3]; exact hp2)) fun s₄ ⟨hr2, o4, k4⟩ => ?_)
  rw [p3] at hr2
  have e4' := e3'.keep k4 (by decide)
  have p4 : val32 s₄.mem B (slot w 0) (2 * w) = p := by rw [Outside.val32 o4 (by omega) (by omega)]; exact p3
  have y4 : val32 s₄.mem B (slot w 4) (2 * w) = y := by
    rw [Outside.val32 o4 (by omega) (by omega), hm3]; exact hY
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hlow : (word s₄.mem B (slot w 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₄.mem B (slot w 0)
    have h2 : val32 s₄.mem B (slot w 0) (2 * w - 1 + 1) =
        w32 s₄.mem B (slot w 0) + 2 ^ 32 * val32 s₄.mem B (slot w 0 + 4) (2 * w - 1) := rfl
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * w), p4] at h2
    omega
  refine WP.mono (Pub.minv_ok e4'.hs e4'.h10 (by omega) hlow) fun s₅ ⟨⟨r12lt, r12inv, m5⟩, k5⟩ => ?_
  have hq : WP isa (.block [.lsl .r30 .r28 1, .add .r30 .r30 .r21, .addi .r31 .r28 0]) s₅ fun t =>
      (t.gpr .r30 = off (off D (2 * k)) 0 ∧ t.gpr .r31 = BitVec.ofNat 64 k ∧ t.mem = s₅.mem) ∧
        Keep [.r30, .r31] s₅ t := by
    refine WP.keep _ ?_ (by decide)
    have g28 : s₅.gpr .r28 = BitVec.ofNat 64 k :=
      (k5.gpr .r28 (by decide)).trans ((k4.gpr .r28 (by decide)).trans
        ((k3.gpr .r28 (by decide)).trans ((k2.gpr .r28 (by decide)).trans ((k1.gpr .r28 (by decide)).trans h28))))
    have g21 : s₅.gpr .r21 = D :=
      (k5.gpr .r21 (by decide)).trans ((k4.gpr .r21 (by decide)).trans
        ((k3.gpr .r21 (by decide)).trans ((k2.gpr .r21 (by decide)).trans ((k1.gpr .r21 (by decide)).trans h21))))
    prun [g28, g21, shl1_ofNat, BitVec.add_zero]
    exact BitVec.add_comm _ _
  refine WP.mono hq fun s₆ ⟨⟨a30, a31, m6⟩, k6⟩ => ?_
  have k16 := ((((k1.trans k2).trans k3).trans k4).trans k5).trans k6
  have e5' := e4'.keep k5 (by decide)
  have g10 : s₆.gpr .r10 = off B (slot w 0) := (k6.gpr .r10 (by decide)).trans e5'.h10
  have g29 : s₆.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := (k6.gpr .r29 (by decide)).trans e5'.h29
  have g11 : s₆.gpr .r11 = BitVec.ofNat 64 (2 * w) := (k6.gpr .r11 (by decide)).trans e5'.h11
  rw [← m5] at hr2 p4 y4
  rw [← m6] at hr2 p4 y4
  have hmq : ∀ i < k, s₆.mem (off (off D (2 * k)) i) = s.mem (off (off D (2 * k)) i) := fun i hi => by
    have hb : Body B w s.mem s₆.mem := by
      rw [m6, m5, ← hm3]; exact Body.of o4 (by omega) (by omega)
    exact hb _ (by
      have := hsep i hi
      by_contra hc
      exact this _ (by simp only [ofs] at hc ⊢; omega) rfl)
  have hbq : Spec.Rsa.bytesAt s₆.mem (off D (2 * k)) k = Spec.Rsa.bytesAt s.mem (off D (2 * k)) k := by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hmq i (List.mem_range.mp hi)
  refine WP.seq (WP.mono (ModExp.powSecret_ok (D := off D (2 * k)) (L := k) (hs.congr k16.wr) (by omega)
    (by omega) (by omega) g10 g29 g11
    (by rw [(k6.gpr .r12 (by decide))]; exact r12lt)
    (by rw [(k6.gpr .r12 (by decide)), m6, m5]; exact r12inv) (by rw [p4]; exact hp2) (by rw [p4]; exact hodd)
    (by rw [hr2, p4]; exact Nat.mod_lt _ (by omega)) a30 a31 hk (by omega)
    (fun i hi => by rw [k16.rd, k16.wr]; exact hrd i hi) hsep)
    fun s₇ ⟨⟨hpow, o7⟩, k7⟩ => ?_)
  rw [hbq, p4, y4, hQ] at hpow
  have v4 := hpow (by rw [hr2, two_pow_128])
  have k17 := k16.trans k7
  have h31 : WP isa (.block [.addi .r31 .r23 0]) s₇ fun t => (t.gpr .r31 = B ∧ t.mem = s₇.mem) ∧ Keep [.r31] s₇ t := by
    refine WP.keep _ ?_ (by decide)
    prun [(k17.gpr .r23 (by decide)).trans h23, BitVec.add_zero]
  refine WP.seq (WP.mono h31 fun s₈ ⟨⟨a31', m8⟩, k8⟩ => ?_)
  have k18 := k17.trans k8
  have e8' : Env s₈ B Z w := ⟨hs.congr k18.wr, (k8.gpr .r10 (by decide)).trans ((k7.gpr .r10 (by decide)).trans g10),
    (k8.gpr .r29 (by decide)).trans ((k7.gpr .r29 (by decide)).trans g29),
    (k8.gpr .r11 (by decide)).trans ((k7.gpr .r11 (by decide)).trans g11), a31', hw, hw', hZ⟩
  refine WP.seq (WP.mono (Pub.oneP_ok e8'.hs (by omega) (by omega) (by omega) e8'.h10 e8'.h29 e8'.h11)
    fun s₉ ⟨⟨v7, o9⟩, k9⟩ => ?_)
  have e9' := e8'.keep k9 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e9' .r3 (a := 4) (b := 7) (by decide) (by decide)) fun s₁₀ ⟨⟨a3, m10⟩, k10⟩ => ?_)
  have v4' : val32 s₉.mem B (slot w 4) (2 * w) = y ^ q % p := by
    rw [Outside.val32 o9 (by omega) (by omega), m8]; exact v4
  rw [v4', v7] at a3
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (if y ^ q % p = 1 then 1 else 0) ∧
    t.mem = s₁₀.mem) (by prun [a3, mask_and_one]; simp) (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨t3, ?_⟩, ?_⟩
  · rw [tm, m10]
    refine Outside.trans (m₂ := s₈.mem) ?_ (Body.of o9 (by omega) (by omega))
    rw [m8]
    refine Outside.trans (m₂ := s₆.mem) ?_ (Body.of_outs o7 fun r hr => ?_)
    · rw [m6, m5, ← hm3]; exact Body.of o4 (by omega) (by omega)
    · simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · exact (((k18.trans k9).trans k10).trans kt).mono (by decide)

/-- Bytes apart from the working space keep their values. -/
theorem Body.bytesAt {B Q : Addr} {Z w k : Nat} {m m' : Mem} (h : Body B w m m') (hZ : slot w 28 ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off Q i ≠ x) : Spec.Rsa.bytesAt m' Q k = Spec.Rsa.bytesAt m Q k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  have := hsep i (List.mem_range.mp hi) (off Q i)
  rw [slot28] at hZ
  show slot w 0 + 28 * (8 * (w + 2)) ≤ ofs B (off Q i)
  by_contra hc
  exact this (by omega) rfl

theorem mask_beq_zero (b : Bool) : (mask b == 0) = !b := by cases b <;> rfl

theorem sub_3k_zero {L k : Nat} (hL : L < 2 ^ 63) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 L - (BitVec.ofNat 64 k <<< 1 + BitVec.ofNat 64 k) == 0) = decide (L = 3 * k) := by
  rw [shl1_ofNat, ← BitVec.ofNat_add]
  by_cases h : L = 3 * k
  · rw [h, show 2 * k + k = 3 * k by omega, BitVec.sub_self]; simp
  · rw [decide_eq_false h]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega

/-- The registers `checkY` writes. -/
def checkYRegs : List Reg := rangeRegs ++ subRegs ++ [.r0, .r3]

/-- `checkY`: `r3 := 1` if `1 < y < p − 1` and, with q (`L = 3 k`),
`y^q mod p = 1`, else 0. -/
theorem checkY_ok {s : State} {B D Y : Addr} {Z w k L : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h26 : s.gpr .r26 = Y) (h27 : s.gpr .r27 = BitVec.ofNat 64 L)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hwk : w = (k + 7) / 8) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hL : L ≤ 3 * k) (hp2 : 2 ≤ arr s.mem B w 0) (hodd : arr s.mem B w 0 % 2 = 1)
    (hrdY : ∀ i < k, InRegions (s.rd ++ s.wr) (off Y i) 1) (hsepY : ∀ i < k, ∀ x, ofs B x < Z → off Y i ≠ x)
    (hrdQ : L = 3 * k → ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1)
    (hsepQ : L = 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x) :
    WP isa checkY s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) < arr s.mem B w 0 - 1) ∧
          (L = 3 * k → Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) ^
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) % arr s.mem B w 0 = 1) then 1 else 0) ∧
        Body B w s.mem t.mem) ∧ Keep checkYRegs s t := by
  have hZ := h.hZ
  generalize hy : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) = y
  generalize hq : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) = q
  generalize hP : arr s.mem B w 0 = p at hp2 hodd
  unfold checkY
  refine WP.seq (WP.mono (range_ok h h23 h26 h28 (by omega) (by omega) hrdY hsepY (by omega))
    fun s₁ ⟨⟨y1, p1, _, a26, b1, a10⟩, k1⟩ => ?_)
  rw [hy, hP] at a26
  rw [hy] at y1
  rw [hP] at p1
  refine WP.ite (s₁.gpr .r26 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [a26, mask_beq_zero, Bool.not_eq_true', decide_eq_false_iff_not] at hb
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 0 ∧ t.mem = s₁.mem) (by prun)
      (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨?_, by rw [tm]; exact b1⟩, (k1.trans kt).mono (by decide)⟩
    rw [t3, ite_eq_right fun hc => hb hc.1]
  · rw [a26, mask_beq_zero, Bool.not_eq_false', decide_eq_true_eq] at hb
    have e1 : Env s₁ B Z w := ⟨h.hs.congr k1.wr, a10, (k1.gpr .r29 (by decide)).trans h.h29,
      (k1.gpr .r11 (by decide)).trans h.h11, (k1.gpr .r31 (by decide)).trans h.h31, h.hw, h.hw', hZ⟩
    refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun t => (t.gpr .r0 == 0) = decide (L = 3 * k) ∧
      t.mem = s₁.mem) (by
        unfold hasQ
        prun [(k1.gpr .r27 (by decide)).trans h27, (k1.gpr .r28 (by decide)).trans h28]
        exact sub_3k_zero (by omega) (by omega)) (by decide)) fun s₂ ⟨⟨a0, m2⟩, k2⟩ => ?_)
    refine WP.ite (s₂.gpr .r0 == 0) (eval_zero _ _) (fun hb' => ?_) (fun hb' => ?_)
    · rw [a0, decide_eq_true_eq] at hb'
      have k12 := k1.trans k2
      have e2 := e1.keep k2 (by decide)
      have hqb : Spec.Rsa.bytesAt s₂.mem (off D (2 * k)) k = Spec.Rsa.bytesAt s.mem (off D (2 * k)) k := by
        rw [m2]; exact b1.bytesAt hZ (hsepQ hb')
      refine WP.mono (subgroup_ok e2 ((k12.gpr .r23 (by decide)).trans h23) ((k12.gpr .r21 (by decide)).trans h21)
        ((k12.gpr .r28 (by decide)).trans h28) (by omega) hk' (by rw [m2, p1]; exact hp2)
        (by rw [m2, p1]; exact hodd) (by rw [k12.rd, k12.wr]; exact hrdQ hb') (hsepQ hb'))
        fun t ⟨⟨t3, bt⟩, kt⟩ => ⟨⟨?_, ?_⟩, (k12.trans kt).mono (by decide)⟩
      · rw [t3, hqb, hq, m2, y1, p1]
        congr 1
        by_cases hpow : y ^ q % p = 1
        · rw [ite_eq_left hpow, ite_eq_left ⟨hb, fun _ => hpow⟩]
        · rw [ite_eq_right hpow, ite_eq_right fun hc => hpow (hc.2 hb')]
      · rw [m2] at bt; exact Outside.trans b1 bt
    · rw [a0, decide_eq_false_iff_not] at hb'
      refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 1 ∧ t.mem = s₂.mem) (by prun)
        (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ =>
          ⟨⟨?_, by rw [tm, m2]; exact b1⟩, ((k1.trans k2).trans kt).mono (by decide)⟩
      rw [t3, ite_eq_left ⟨hb, fun hc => absurd hc hb'⟩]

end VG.Proof.Ffdh.PPC64LE.Domain
