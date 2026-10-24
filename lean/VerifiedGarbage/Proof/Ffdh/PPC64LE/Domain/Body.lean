module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Domain
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

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
        Body B w s.mem t.mem) ∧ Keep rangeRegs s t := by
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
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
  · exact ((((((((((k13.trans k35).trans k6).trans k7).trans k8).trans k9).trans k10).trans k11).trans
      k12').trans kt).mono (by decide))

end VG.Proof.Ffdh.PPC64LE.Domain
