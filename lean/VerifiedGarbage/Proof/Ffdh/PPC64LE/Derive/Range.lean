module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Derive
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Body
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# FFDH's private keys on PPC64LE: x's range

In the working space of `Domain/Body.lean`, p in array 0: `xLoadPre_ok` and
`xLoadRest_ok`, x's octets (whose address and length are in the header's
words 8 and 9) into array 4; `xBound_ok`, the bound (q, or `p − 1` in array
6) into `r10`'s array; `xMask_ok`, the mask of `0 < x < bound`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Derive

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.Derive
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)

/-- The bound on x: q (the `k` octets at `D + 2 k`) if `L = 3 k`, else
`p − 1`. -/
def bnd (m : Mem) (D : Addr) (k L p : Nat) : Nat :=
  if L = 3 * k then Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D (2 * k)) k) else p - 1

/-- `xLoadPre`: array 4's base, and x's address and length from the header. -/
theorem xLoadPre_ok {s : State} {B X : Addr} {Z w xl : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hXL : s.mem.readW (off B 72) 64 = BitVec.ofNat 64 xl) :
    WP isa (.block xLoadPre) s fun t =>
      (t.gpr .r10 = off B (slot w 4) ∧ t.gpr .r12 = off X 0 ∧ t.gpr .r6 = BitVec.ofNat 64 xl ∧ t.mem = s.mem) ∧
        Keep [.r6, .r10, .r12] s t := by
  have hZ := h.hZ
  have e28 := slot_eq w 28
  unfold xLoadPre
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r10) (by decide) (by decide) 4) fun s₁ ⟨⟨a10, m1⟩, k1⟩ => ?_
  rw [← m1] at hX hXL
  refine WP.mono (WP.keep [.r12, .r6] (Q := fun t => t.gpr .r12 = off X 0 ∧ t.gpr .r6 = BitVec.ofNat 64 xl ∧
      t.mem = s₁.mem) ?_ (by decide)) fun t ⟨⟨a12, a6, mt⟩, kt⟩ =>
    ⟨⟨(kt.gpr .r10 (by decide)).trans a10, a12, a6, by rw [mt, m1]⟩, (k1.trans kt).mono (by decide)⟩
  prun [(k1.gpr .r23 (by decide)).trans h23, (h.hs.congr k1.wr).ld (d := 64) (n := 8) (by omega),
    (h.hs.congr k1.wr).ld (d := 72) (n := 8) (by omega), hX, hXL]

/-- `xLoadRest`: x's `xl` octets (at `r12`, `xl` in `r6`) into array 4 as
`2 w` digits, its word `w` := 0, and `r10` back to array 0. -/
theorem xLoadRest_ok {s : State} {B X : Addr} {Z w xl : Nat} (hs : Scr s B Z) (h23 : s.gpr .r23 = B)
    (h10 : s.gpr .r10 = off B (slot w 4)) (h12 : s.gpr .r12 = off X 0) (h6 : s.gpr .r6 = BitVec.ofNat 64 xl)
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hk : 1 ≤ xl) (hkw : xl ≤ 8 * w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hrd : ∀ i < xl, InRegions (s.rd ++ s.wr) (off X i) 1) (hsep : ∀ i < xl, ∀ x, ofs B x < Z → off X i ≠ x) :
    WP isa xLoadRest s fun t =>
      (arr t.mem B w 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) ∧
        word t.mem B (slot w 4 + 8 * w) = 0 ∧ Outside B (slot w 4) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .r10 = off B (slot w 0)) ∧
      Keep [.r0, .r10, .r14, .r15, .r16, .r17] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e4 := e 4; have e5 := e 5; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  unfold xLoadRest
  refine WP.seq (WP.mono (loadN_ok (dA := slot w 4) hs h10 h12 h6 h11 hk hkw hw' (by omega) (by omega) hrd hsep)
    fun s₃ ⟨hv, out₃, k3⟩ => ?_)
  refine WP.mono (WP.keep [.r14, .r0, .r10] (Q := fun t =>
    t.mem = s₃.mem.writeW (off B (slot w 4 + 8 * w)) (0 : BitVec 64) ∧ t.gpr .r10 = off B (slot w 0))
    ?_ (by decide)) fun t ⟨⟨tm, t10⟩, k4⟩ => ⟨⟨?_, ?_, ?_, t10⟩, (k3.trans k4).mono (by decide)⟩
  · have a10' : s₃.gpr .r10 = off B (slot w 4) := (k3.gpr _ (by decide)).trans h10
    have e16 : off B (slot w 4 + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w 4 + 8 * w) := by
      rw [off, VG.Offset.add_ofNat_sub B (show 16 ≤ slot w 4 + 8 * (w + 2) by omega)]; congr 2
    prun [a10', (k3.gpr .r29 (by decide)).trans h29, (k3.gpr .r23 (by decide)).trans h23, off_add, e16, hh,
      BitVec.add_zero, (hs.congr k3.wr).st (show slot w 4 + 8 * w + 8 ≤ Z by omega)]
    exact ⟨rfl, by simp [off, slot, hh]⟩
  · rw [arr, tm, Mont.Outside.val32 (fun x hx => writeW_outside s₃.mem B (d := slot w 4 + 8 * w) 0 (by omega) x hx)
      (by omega) (by omega)]
    exact hv
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (out₃.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside s₃.mem B (d := slot w 4 + 8 * w) 0 (by omega)).mono (by omega) (by omega))

/-- `xBound`: `r10 :=` array 1 with q's `k` octets (at `D + 2 k`) if
`L = 3 k`, else array 6. -/
theorem xBound_ok {s : State} {B D : Addr} {Z w k L : Nat} (h : Env s B Z w)
    (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hL : L < 2 ^ 63) (hk32 : k < 2 ^ 32)
    (hrdQ : L = 3 * k → ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1)
    (hsepQ : L = 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x) :
    WP isa xBound s fun t =>
      ((∃ j, (j = 1 ∨ j = 6) ∧ t.gpr .r10 = off B (slot w j) ∧
          val32 t.mem B (slot w j) (2 * w) = if L = 3 * k then
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) else val32 s.mem B (slot w 6) (2 * w)) ∧
        Outside B (slot w 1) (8 * w) s.mem t.mem) ∧ Keep [.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] s t := by
  have hZ := h.hZ
  have hw' := h.hw'
  have e1 := slot_eq w 1; have e28 := slot_eq w 28
  unfold xBound
  refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun t => (t.gpr .r0 == 0) = decide (L = 3 * k) ∧
    t.mem = s.mem) (by
      unfold hasQ
      prun [h27, h28]
      exact sub_3k_zero hL hk32) (by decide)) fun s₁ ⟨⟨a0, m1⟩, k1⟩ => ?_)
  have e1' := h.keep k1 (by decide)
  refine WP.ite (s₁.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [a0, decide_eq_true_eq] at hb
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off (off D (2 * k)) 0 ∧
      t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s₁.mem) (by
        prun [(k1.gpr .r21 (by decide)).trans h21, (k1.gpr .r28 (by decide)).trans h28, shl1_ofNat,
          BitVec.add_zero]
        exact BitVec.add_comm _ _) (by decide)) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_
    have e2 := e1'.keep k2 (by decide)
    refine WP.mono (e2.base (rd := .r10) (by decide) (by decide) 1) fun s₃ ⟨⟨a10, m3⟩, k3⟩ => ?_
    have k13 := (k1.trans k2).trans k3
    refine WP.mono (loadN_ok (dA := slot w 1) (h.hs.congr k13.wr) a10 ((k3.gpr .r12 (by decide)).trans a12)
      ((k3.gpr .r6 (by decide)).trans a6) ((k13.gpr .r11 (by decide)).trans h.h11) hk hkw (by omega)
      (by omega) (by omega) (by rw [k13.rd, k13.wr]; exact hrdQ hb) (hsepQ hb))
      fun t ⟨hv, out, kt⟩ => ⟨⟨⟨1, Or.inl rfl, (kt.gpr .r10 (by decide)).trans a10, ?_⟩, ?_⟩,
        (k13.trans kt).mono (by decide)⟩
    · rw [hv, ite_eq_left hb, m3, m2, m1]
    · rw [m3, m2, m1] at out; exact out
  · rw [a0, decide_eq_false_iff_not] at hb
    refine WP.mono (e1'.base (rd := .r10) (by decide) (by decide) 6) fun t ⟨⟨a10, mt⟩, kt⟩ =>
      ⟨⟨⟨6, Or.inr rfl, a10, by rw [ite_eq_right hb, mt, m1]⟩, by rw [mt, m1]; exact Outside.refl _ _ _ _⟩,
        (k1.trans kt).mono (by decide)⟩

/-- The registers `xMask` writes. -/
def xMaskRegs : List Reg := constsRegs ++ ([.r4, .r6, .r12, .r19, .r26] : List Reg)

/-- `xMask`: with x in array 4 (its word `w` zero) and p in array 0,
`r26 :=` the mask of `0 < x < bnd`. -/
theorem xMask_ok {s : State} {B D : Addr} {Z w k L x : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hL : L < 2 ^ 63) (hk32 : k < 2 ^ 32)
    (hrdQ : L = 3 * k → ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1)
    (hsepQ : L = 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x)
    (hx : arr s.mem B w 4 = x) (htop : word s.mem B (slot w 4 + 8 * w) = 0) (hp : 1 ≤ arr s.mem B w 0) :
    WP isa xMask s fun t =>
      (t.gpr .r26 = mask (decide (0 < x ∧ x < bnd s.mem D k L (arr s.mem B w 0))) ∧
        arr t.mem B w 0 = arr s.mem B w 0 ∧ Body B w s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
      Keep xMaskRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e1 := slot_eq w 1; have e3 := slot_eq w 3; have e4 := slot_eq w 4
  have e5 := slot_eq w 5; have e6 := slot_eq w 6; have e7 := slot_eq w 7; have e8 := slot_eq w 8
  have e28 := slot_eq w 28
  generalize hb : bnd s.mem D k L (arr s.mem B w 0) = b
  generalize hP : arr s.mem B w 0 = p at hp hb
  unfold xMask
  refine WP.seq (WP.mono (consts_ok h h23 (by rw [hP]; exact hp)) fun s₁ ⟨⟨v7, v6, v5, o1, a10⟩, k1⟩ => ?_)
  rw [hP] at v6
  have e1' : Env s₁ B Z w := ⟨hs.congr k1.wr, a10, (k1.gpr .r29 (by decide)).trans h.h29,
    (k1.gpr .r11 (by decide)).trans h.h11, (k1.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  have x1 : val32 s₁.mem B (slot w 4) (2 * w) = x := by rw [Outside.val32 o1 (by omega) (by omega)]; exact hx
  have p1 : val32 s₁.mem B (slot w 0) (2 * w) = p := by rw [Outside.val32 o1 (by omega) (by omega)]; exact hP
  have t1 : word s₁.mem B (slot w 4 + 8 * w) = 0 := by rw [Outside.word o1 (by omega) (by omega)]; exact htop
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (e1'.base (rd := .r8) (by decide) (by decide) 4) fun s₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  refine WP.mono ((e1'.keep k2 (by decide)).base (rd := .r9) (by decide) (by decide) 3)
    fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have k23 := k2.trans k3
  have e3' := e1'.keep k23 (by decide)
  have hm3 : s₃.mem = s₁.mem := by rw [m3, m2]
  have k13 := k1.trans k23
  refine WP.seq (WP.mono (xBound_ok e3' ((k13.gpr .r21 (by decide)).trans h21)
    ((k13.gpr .r27 (by decide)).trans h27) ((k13.gpr .r28 (by decide)).trans h28) hk hkw hL hk32
    (fun hq => by rw [k13.rd, k13.wr]; exact hrdQ hq) hsepQ) fun s₄ ⟨⟨⟨j, hj, a10₄, v4⟩, o4⟩, k4⟩ => ?_)
  rw [hm3] at v4 o4
  have hbv : val32 s₄.mem B (slot w j) (2 * w) = b := by
    rw [v4, ← hb]
    unfold bnd
    by_cases hq : L = 3 * k
    · rw [ite_eq_left hq, ite_eq_left hq, Body.bytesAt (Body.of o1 (by omega) (by omega)) hZ (hsepQ hq)]
    · rw [ite_eq_right hq, ite_eq_right hq]; exact v6
  have x4 : val32 s₄.mem B (slot w 4) (2 * w) = x := by rw [Outside.val32 o4 (by omega) (by omega)]; exact x1
  have t4 : word s₄.mem B (slot w 4 + 8 * w) = 0 := by rw [Outside.word o4 (by omega) (by omega)]; exact t1
  have k14 := k13.trans k4
  have hj' : slot w 3 + 4 * (2 * w) ≤ slot w j ∨ slot w j + 4 * (2 * w) ≤ slot w 3 := by
    rcases hj with rfl | rfl <;> simp only [slot_eq] <;> omega
  have hjZ : slot w j + 4 * (2 * w) ≤ Z := by rcases hj with rfl | rfl <;> simp only [slot_eq] <;> omega
  refine WP.seq (WP.mono (subMod_ok (dA := slot w 4) (dT := slot w 3) (dM := slot w j) (n := 2 * w)
    (hs.congr k14.wr) ((k4.gpr .r8 (by decide)).trans ((k3.gpr .r8 (by decide)).trans a8))
    ((k4.gpr .r9 (by decide)).trans a9) a10₄ ((k4.gpr .r11 (by decide)).trans e3'.h11) (by omega) (by omega)
    (by omega) (by omega) hjZ (by omega) hj') fun s₅ ⟨⟨c, hc, hv, h20⟩, o5, k5⟩ => ?_)
  have hw32 : w32 s₄.mem B (slot w 4 + 4 * (2 * w)) = 0 := by
    have := word_eq_w32 s₄.mem B (slot w 4 + 8 * w)
    rw [t4, show (0 : BitVec 64).toNat = 0 from rfl] at this
    rw [show slot w 4 + 4 * (2 * w) = slot w 4 + 8 * w by omega]; omega
  have hlt : (w32 s₄.mem B (slot w 4 + 4 * (2 * w)) < c) ↔ x < b := by
    have hT := val32_lt s₅.mem B (slot w 3) (2 * w)
    have hA := val32_lt s₄.mem B (slot w 4) (2 * w)
    have hM := val32_lt s₄.mem B (slot w j) (2 * w)
    rw [hw32]; rw [x4, hbv] at hv; rw [x4] at hA; rw [hbv] at hM
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
    · omega
    · rw [show 32 * (2 * w) = 64 * w by omega] at hT hv hA hM; omega
  rw [mask_ite] at h20
  simp only [hlt] at h20
  have k15 := k14.trans k5
  have hblk : WP isa (.block [.addi .r26 .r20 0, .addi .r10 .r23 hdrBytes]) s₅ fun t =>
      (t.gpr .r26 = mask (decide (x < b)) ∧ t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₅.mem) ∧
        Keep [.r10, .r26] s₅ t := by
    have hh : hdrBytes = 256 := rfl
    refine WP.keep _ ?_ (by decide)
    prun [h20, (k15.gpr .r23 (by decide)).trans h23, hh, BitVec.add_zero]
    simp [off, slot, hh]
  refine WP.seq (WP.mono hblk fun s₆ ⟨⟨a26, a10₆, m6⟩, k6⟩ => ?_)
  have k56 := (k4.trans k5).trans k6
  have e6' : Env s₆ B Z w := ⟨hs.congr (k15.trans k6).wr, a10₆, (k56.gpr .r29 (by decide)).trans e3'.h29,
    (k56.gpr .r11 (by decide)).trans e3'.h11, (k56.gpr .r31 (by decide)).trans e3'.h31, hw, hw', hZ⟩
  refine WP.seq (WP.mono (eqMask_ok e6' .r19 (a := 4) (b := 5) (by decide) (by decide))
    fun s₇ ⟨⟨a19, m7⟩, k7⟩ => ?_)
  refine WP.mono (clear19_ok s₇ ((k7.gpr .r26 (by decide)).trans a26) a19) fun t ⟨⟨t26, mt⟩, kt⟩ => ?_
  have o5' : Outside B (slot w 3) (8 * w) s₄.mem s₆.mem := by
    rw [m6]; exact Outside.mono o5 (Nat.le_refl _) (by omega)
  have x6 : val32 s₆.mem B (slot w 4) (2 * w) = x := by rw [Outside.val32 o5' (by omega) (by omega)]; exact x4
  have z6 : val32 s₆.mem B (slot w 5) (2 * w) = 0 := by
    rw [Outside.val32 o5' (by omega) (by omega), Outside.val32 o4 (by omega) (by omega)]; exact v5
  have p6 : val32 s₆.mem B (slot w 0) (2 * w) = p := by
    rw [Outside.val32 o5' (by omega) (by omega), Outside.val32 o4 (by omega) (by omega)]; exact p1
  have hmt : t.mem = s₆.mem := by rw [mt, m7]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [t26, x6, z6]
    congr 1
    by_cases h0 : x = 0
    · subst h0; simp
    · have : 0 < x := Nat.pos_of_ne_zero h0
      simp [h0, this]
  · rw [arr, hmt]; exact p6
  · rw [hmt]
    refine Outside.trans (m₂ := s₄.mem) ?_ (Body.of o5' (by omega) (by omega))
    exact Outside.trans (Body.of o1 (by omega) (by omega)) (Body.of o4 (by omega) (by omega))
  · exact ((k7.trans kt).gpr .r10 (by decide)).trans a10₆
  · exact (((k15.trans k6).trans k7).trans kt).mono (by decide)

end VG.Proof.Ffdh.PPC64LE.Derive
