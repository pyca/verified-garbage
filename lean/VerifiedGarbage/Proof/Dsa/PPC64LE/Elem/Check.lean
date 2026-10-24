module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Basic
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.Range
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx

/-!
# DSA on PPC64LE: the two checks of g and y

In the P space, with p in array 0 and the number in array 4:

* `elemRange_ok`: `r0 = 0` exactly when `1 < [4] < [0]`;
* `elemOrder_ok`: `r0 = 0` exactly when `[4]^q mod p = 1`, with `R² mod p`
  in array 8.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- The registers `elemRange` writes. -/
def elemRangeRegs : List Reg := [.r0, .r3, .r4, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r19, .r20]

/-- `elemRange`: `r0 = 0` exactly when `1 < [4] < [0]`, with `[4]`'s word `w`
zero; arrays 3, 5 and 7 change. -/
theorem elemRange_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w)
    (top : word s.mem B (slot w 4 + 8 * w) = 0) :
    WP isa elemRange s fun t =>
      ((t.gpr .r0 = 0 ↔ 1 < arr s.mem B w 4 ∧ arr s.mem B w 4 < arr s.mem B w 0) ∧
        arr t.mem B w 4 = arr s.mem B w 4 ∧ Outside B (slot w 3) (5 * (8 * (w + 2))) s.mem t.mem ∧
        Env t B Z w) ∧ Keep elemRangeRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e3 := slot_eq w 3; have e4 := slot_eq w 4; have e5 := slot_eq w 5
  have e7 := slot_eq w 7; have e8 := slot_eq w 8; have e28 := slot_eq w 28
  unfold elemRange
  refine WP.seq (WP.mono (Pub.oneP_ok hs (by omega) (by omega) (by omega) h.h10 h.h29 h.h11)
    fun s₁ ⟨⟨v7, o1⟩, k1⟩ => ?_)
  have en1 := h.keep k1 (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₁.mem) (by
      prun [en1.h31, hdrBytes]
      rw [show slot w 0 = 256 by simp [slot, hdrBytes]]) (by decide)) fun s₂ ⟨⟨a10, m2⟩, k2⟩ => ?_
  have en2 := env_keep10 en1 k2 (by decide) a10
  refine WP.mono (en2.base (rd := .r14) (by decide) (by decide) 5) fun s₃ ⟨⟨a14, m3⟩, k3⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (en2.hs.congr k3.wr) a14 ((k3.gpr .r11 (by decide)).trans en2.h11)
    (by omega) (by omega) (by omega)) fun s₄ ⟨⟨_, hz, o4⟩, k4⟩ => ?_)
  have en4 := (en2.keep k3 (by decide)).keep k4 (by decide)
  have hm3 : s₃.mem = s₁.mem := by rw [m3, m2]
  have v5 : arr s₄.mem B w 5 = 0 := by
    rw [arr, Pre.val32_eq_wv]
    exact (VG.Proof.Bignum.wv_eq_zero_iff _ _ _ _).mpr hz
  have v7' : arr s₄.mem B w 7 = 1 := by rw [arr, Outside.val32 o4 (by omega) (by omega), hm3]; exact v7
  have v4 : arr s₄.mem B w 4 = arr s.mem B w 4 := by
    rw [arr, Outside.val32 o4 (by omega) (by omega), hm3, Outside.val32 o1 (by omega) (by omega)]
  have v0 : arr s₄.mem B w 0 = arr s.mem B w 0 := by
    rw [arr, Outside.val32 o4 (by omega) (by omega), hm3, Outside.val32 o1 (by omega) (by omega)]
  have top4 : word s₄.mem B (slot w 4 + 8 * w) = 0 := by
    rw [Outside.word o4 (by omega) (by omega), hm3, Outside.word o1 (by omega) (by omega)]; exact top
  refine subLt_ok en4 (a := 4) (by decide) (by decide) top4 fun s₅ h20 o5 k5 => ?_
  rw [v4, v0] at h20
  have en5 := en4.keep k5 (by decide)
  have hn : slot w 28 ≤ 2 ^ 64 := by omega
  have q5 : ∀ j, j < 28 → j ≠ 3 → arr s₅.mem B w j = arr s₄.mem B w j := fun j hj h3 =>
    Outside.arrEq o5 hj h3 hn
  refine WP.seq (WP.mono (eqMask_ok en5 .r19 (a := 4) (b := 5) (by decide) (by decide))
    fun s₆ ⟨⟨a19, m6⟩, k6⟩ => ?_)
  rw [← arr, ← arr, q5 4 (by decide) (by decide), q5 5 (by decide) (by decide), v4, v5] at a19
  refine WP.seq (WP.mono (clear20_ok s₆ ((k6.gpr .r20 (by decide)).trans h20) a19) fun s₇ ⟨⟨b20, m7⟩, k7⟩ => ?_)
  have en7 := (en5.keep k6 (by decide)).keep k7 (by decide)
  refine WP.seq (WP.mono (eqMask_ok en7 .r19 (a := 4) (b := 7) (by decide) (by decide))
    fun s₈ ⟨⟨c19, m8⟩, k8⟩ => ?_)
  have hm7 : s₇.mem = s₅.mem := by rw [m7, m6]
  rw [hm7, ← arr, ← arr, q5 4 (by decide) (by decide), q5 7 (by decide) (by decide), v4, v7'] at c19
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (clear20_ok s₈ ((k8.gpr .r20 (by decide)).trans b20) c19) fun s₉ ⟨⟨c20, m9⟩, k9⟩ => ?_
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = s₉.gpr .r20 ∧ t.mem = s₉.mem)
    (by prun [BitVec.add_zero]) (by decide)) fun s₁₀ ⟨⟨a3, m10⟩, k10⟩ => ?_
  refine WP.mono (unmask_ok s₁₀ (a3.trans c20)) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have hmt : t.mem = s₅.mem := by rw [mt, m10, m9, m8, hm7]
  refine ⟨⟨?_, ?_, ?_, ((((en7.keep k8 (by decide)).keep k9 (by decide)).keep k10 (by decide)).keep kt
    (by decide))⟩, (((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans
      k9).trans k10 |>.trans kt).mono (by decide)⟩
  · rw [t0]
    generalize arr s.mem B w 4 = x
    generalize arr s.mem B w 0 = p
    by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> by_cases hl : x < p <;> simp [h0, h1, hl] <;> omega
  · rw [hmt, q5 4 (by decide) (by decide), v4]
  · have o1' : Outside B (slot w 7) (8 * w) s.mem s₁.mem := o1
    have o4' : Outside B (slot w 5) (8 * w) s₁.mem s₄.mem := by rw [← hm3]; exact o4
    rw [hmt]
    exact ((o1'.mono (by omega) (by omega)).trans (o4'.mono (by omega) (by omega))).trans
      (o5.mono (by omega) (by omega))

/-- The registers `elemOrder` writes. -/
def elemOrderRegs : List Reg := copyRegs ++ [.r4, .r6, .r12, .r30, .r31] ++ ModExp.powSRegs

/-- `elemOrder`, in the P space with p (odd, at least 2) in array 0 and
`R² mod p` in array 8: `r0 = 0` exactly when `[4]^q mod p = 1`; arrays 1–7
change. -/
theorem elemOrder_ok {s : State} {L : Lay} {key sig dig : Addr} {p : Nat} (hL : L.Ok)
    (hr : Regs s L key sig dig) (hin : InP s L) (hk : Src s L key (3 * L.pl + L.ql))
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 8 = 2 ^ (128 * L.wp) % p) :
    WP isa elemOrder s fun t =>
      ((t.gpr .r0 = 0 ↔ arrP s.mem L 4 ^ qOf s.mem L key % p = 1) ∧ InP t L ∧
        Outside L.S (slot L.wp 1) (7 * (8 * (L.wp + 2))) s.mem t.mem) ∧ Keep elemOrderRegs s t := by
  have hZ := hL.hdr
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hql := hL.ql
  have hqZ : L.qOff + 1600 ≤ L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have e0 := slot_eq L.wp 0; have e1 := slot_eq L.wp 1; have e4 := slot_eq L.wp 4; have e7 := slot_eq L.wp 7
  have e8 := slot_eq L.wp 8; have e28 := slot_eq L.wp 28
  have en := hin.env
  unfold elemOrder
  refine WP.seq (WP.mono (copy_ok en (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₁ ⟨⟨v1, o1⟩, k1⟩ => ?_)
  have pb1 : PBody L s.mem s₁.mem := o1.mono (by omega) (by omega)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrQ_ok (hr.keep k1)) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_
  refine WP.mono (WP.keep [.r30, .r31] (Q := fun t => t.gpr .r30 = off (off key L.pl) 0 ∧
    t.gpr .r31 = BitVec.ofNat 64 L.ql ∧ t.mem = s₂.mem) (by prun [a12, a6, BitVec.add_zero]) (by decide))
    fun s₃ ⟨⟨a30, a31, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have g10 : s₃.gpr .r10 = off L.S (slot L.wp 0) := (k13.gpr .r10 (by decide)).trans en.h10
  have hm3 : s₃.mem = s₁.mem := by rw [m3, m2]
  have p3 : val32 s₃.mem L.S (slot L.wp 0) (2 * L.wp) = p := by
    rw [hm3, Outside.val32 o1 (by omega) (by omega)]; exact hp0
  have hlow : (word s₃.mem L.S (slot L.wp 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₃.mem L.S (slot L.wp 0)
    have h2 : val32 s₃.mem L.S (slot L.wp 0) (2 * L.wp - 1 + 1) =
        w32 s₃.mem L.S (slot L.wp 0) + 2 ^ 32 * val32 s₃.mem L.S (slot L.wp 0 + 4) (2 * L.wp - 1) := rfl
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * L.wp), p3] at h2
    omega
  refine WP.mono (Pub.minv_ok (en.hs.congr k13.wr) g10 (by omega) hlow) fun s₄ ⟨⟨r12lt, r12inv, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have p4 : val32 s₄.mem L.S (slot L.wp 0) (2 * L.wp) = p := by rw [m4]; exact p3
  have r1 : val32 s₄.mem L.S (slot L.wp 1) (2 * L.wp) = 2 ^ (128 * L.wp) % p := by
    rw [m4, hm3]; exact v1.trans hrr
  have y4 : val32 s₄.mem L.S (slot L.wp 4) (2 * L.wp) = arrP s.mem L 4 := by
    rw [m4, hm3, Outside.val32 o1 (by omega) (by omega)]
  have hq4 : Spec.Rsa.bytesAt s₄.mem (off key L.pl) L.ql = Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql := by
    rw [m4, hm3]; exact (hk.sub (o := L.pl) (k := L.ql) (by omega)).bytesPre (Nat.le_refl _) (pb1.body hL) hZ
  refine WP.seq (WP.mono (ModExp.powSecret_ok (D := off key L.pl) (L := L.ql) (en.hs.congr k14.wr) (by omega)
    (by omega) (by omega) ((k4.gpr .r10 (by decide)).trans g10) ((k14.gpr .r29 (by decide)).trans en.h29)
    ((k14.gpr .r11 (by decide)).trans en.h11) r12lt (by rw [m4]; exact r12inv) (by rw [p4]; exact hp)
    (by rw [p4]; exact hpo) (by rw [r1, p4]; exact Nat.mod_lt _ (by omega)) ((k4.gpr .r30 (by decide)).trans a30)
    ((k4.gpr .r31 (by decide)).trans a31) (by omega) (by omega)
    (fun i hi => by rw [k14.rd, k14.wr]; exact (hk.sub (o := L.pl) (k := L.ql) (by omega)).rd i hi)
    (fun i hi x hx => (hk.sub (o := L.pl) (k := L.ql) (by omega)).sep i hi x
      (Nat.lt_of_lt_of_le hx (by omega : L.qOff ≤ L.Z)))) fun s₅ ⟨⟨hpow, o5⟩, k5⟩ => ?_)
  rw [hq4, p4, y4] at hpow
  have v4 := hpow (by rw [r1, ← Nat.pow_add, show 64 * L.wp + 64 * L.wp = 128 * L.wp by omega])
  have k15 := k14.trans k5
  have k15' : Keep elemOrderRegs s s₅ := k15.mono (by decide)
  have k25 := (((k2.trans k3).trans k4).trans k5)
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = L.S ∧ t.mem = s₅.mem) (by
      prun [(k15.gpr .r23 (by decide)).trans hin.h23, BitVec.add_zero]) (by decide)) fun s₆ ⟨⟨a31', m6⟩, k6⟩ => ?_)
  have en6 := env_keep31 en (k15.trans k6) (by decide) a31'
  refine WP.seq (WP.mono (Pub.oneP_ok en6.hs (by omega) (by omega) (by omega) en6.h10 en6.h29 en6.h11)
    fun s₇ ⟨⟨v7, o7⟩, k7⟩ => ?_)
  have en7 := en6.keep k7 (by decide)
  refine WP.seq (WP.mono (eqMask_ok en7 .r3 (a := 4) (b := 7) (by decide) (by decide)) fun s₈ ⟨⟨a3, m8⟩, k8⟩ => ?_)
  refine WP.mono (unmask_ok s₈ a3) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have o7' : Outside L.S (slot L.wp 7) (8 * L.wp) s₆.mem s₇.mem := o7
  have k6t := ((k6.trans k7).trans k8).trans kt
  have hmt : t.mem = s₇.mem := by rw [mt, m8]
  refine ⟨⟨?_, ⟨en7.keep ((k8.trans kt)) (by decide), ((k1.trans k25).trans k6t).gpr .r21 (by decide) |>.trans hin.h21,
    ((k1.trans k25).trans k6t).gpr .r23 (by decide) |>.trans hin.h23⟩, ?_⟩, (k15'.trans k6t).mono (by decide)⟩
  · rw [t0, v7, Outside.val32 o7' (by omega) (by omega), m6, v4, decide_eq_true_iff]
    exact Iff.rfl
  · have o5' : Outside L.S (slot L.wp 1) (slot L.wp 8 - slot L.wp 1) s₄.mem s₅.mem := outs_within o5 fun r hr => by
      simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [slot_eq, slot_eq] <;> omega
    rw [m4, hm3] at o5'
    rw [m6] at o7'
    rw [hmt]
    exact ((o1.mono (by omega) (by omega)).trans (o5'.mono (by omega) (by omega))).trans
      (o7'.mono (by omega) (by omega))

end VG.Proof.Dsa.PPC64LE
