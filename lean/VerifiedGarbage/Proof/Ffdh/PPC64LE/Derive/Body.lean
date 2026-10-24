module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Range
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeBody
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_derive_public` on PPC64LE: after p's check

In the working space of `Domain/Body.lean`, p in array 0, x's address and
length and `y`'s address in the header's words 8–10: `dpBody_ok`, x's range
(`xRange`), then zeros and status 2 (`dpBad`), or `g^x mod p` or zeros and
status 1 or 3 (`dpGood`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Derive

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.Derive
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)

/-- `status`: `r3 := 3 − 2 r3`, for `r3` 1 or 0. -/
theorem status_ok (s : State) (c : Prop) [Decidable c] (h3 : s.gpr .r3 = BitVec.ofNat 64 (if c then 1 else 0)) :
    WP isa (.block status) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if c then 1 else 3) ∧ t.mem = s.mem) ∧ Keep [.r0, .r3] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold status
  prun [h3]
  by_cases hc : c <;> simp [hc] <;> rfl

/-- The registers `xRange` writes. -/
def xRangeRegs : List Reg := xMaskRegs ++ ([.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] : List Reg)

/-- `xRange`: x's `xl` octets (the header's words 8 and 9) into array 4, and
`r26 :=` the mask of `0 < x < bnd`. -/
theorem xRange_ok {s : State} {B D X : Addr} {Z w k L xl : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hL : L < 2 ^ 63) (hk32 : k < 2 ^ 32) (hxl : 1 ≤ xl) (hxk : xl ≤ k)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hXL : s.mem.readW (off B 72) 64 = BitVec.ofNat 64 xl)
    (hrdX : ∀ i < xl, InRegions (s.rd ++ s.wr) (off X i) 1) (hsepX : ∀ i < xl, ∀ x, ofs B x < Z → off X i ≠ x)
    (hrdQ : L = 3 * k → ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1)
    (hsepQ : L = 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x) (hp : 1 ≤ arr s.mem B w 0) :
    WP isa xRange s fun t =>
      (t.gpr .r26 = mask (decide (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) < bnd s.mem D k L (arr s.mem B w 0))) ∧
        arr t.mem B w 0 = arr s.mem B w 0 ∧ Body B w s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
      Keep xRangeRegs s t := by
  have hZ := h.hZ
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e4 := slot_eq w 4; have e8 := slot_eq w 8; have e28 := slot_eq w 28
  unfold xRange
  refine WP.seq (WP.mono (xLoadPre_ok h h23 hX hXL) fun s₁ ⟨⟨a10, a12, a6, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (xLoadRest_ok (h.hs.congr k1.wr) ((k1.gpr .r23 (by decide)).trans h23) a10 a12 a6
    ((k1.gpr .r29 (by decide)).trans h.h29) ((k1.gpr .r11 (by decide)).trans h.h11) hxl (by omega) (by omega)
    (by omega) (by rw [k1.rd, k1.wr]; exact hrdX) hsepX) fun s₂ ⟨⟨x2, top2, o2, a10₂⟩, k2⟩ => ?_)
  rw [m1] at x2 o2
  have k12 := k1.trans k2
  have e2 : Env s₂ B Z w := ⟨h.hs.congr k12.wr, a10₂, (k12.gpr .r29 (by decide)).trans h.h29,
    (k12.gpr .r11 (by decide)).trans h.h11, (k12.gpr .r31 (by decide)).trans h.h31, h.hw, hw', hZ⟩
  have b2 : Body B w s.mem s₂.mem := Body.of o2 (by omega) (by omega)
  have p2 : arr s₂.mem B w 0 = arr s.mem B w 0 := by rw [arr, Outside.val32 o2 (by omega) (by omega)]
  have hq2 : bnd s₂.mem D k L (arr s.mem B w 0) = bnd s.mem D k L (arr s.mem B w 0) := by
    unfold bnd
    by_cases hq : L = 3 * k
    · rw [ite_eq_left hq, ite_eq_left hq, b2.bytesAt hZ (hsepQ hq)]
    · rw [ite_eq_right hq, ite_eq_right hq]
  refine WP.mono (xMask_ok e2 ((k12.gpr .r23 (by decide)).trans h23) ((k12.gpr .r21 (by decide)).trans h21)
    ((k12.gpr .r27 (by decide)).trans h27) ((k12.gpr .r28 (by decide)).trans h28) hk hkw hL hk32
    (fun hq => by rw [k12.rd, k12.wr]; exact hrdQ hq) hsepQ x2 top2 (by rw [p2]; exact hp))
    fun t ⟨⟨t26, tp, tb, t10⟩, kt⟩ => ⟨⟨?_, by rw [tp, p2], Outside.trans b2 tb, t10⟩, (k12.trans kt).mono (by decide)⟩
  rw [t26, p2, hq2]

/-- The registers `dpBody` writes. -/
def dpBodyRegs : List Reg :=
  xRangeRegs ++ exPowRegs ++ exOutRegs ++ ([.r0, .r3, .r9, .r15, .r16, .r17, .r27] : List Reg)

/-- `dpBody`: zeros and 2 if x is out of range; else `z = g^x mod p` (g's `k`
octets at `D + k`) or zeros at `O` and 1 or 3. -/
theorem dpBody_ok {s : State} {B D X O : Addr} {Z w k L xl p x g b : Nat} (h : Env s B Z w)
    (h23 : s.gpr .r23 = B) (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hwk : w = (k + 7) / 8) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hL : L = 2 * k ∨ L = 3 * k) (hxl : 1 ≤ xl) (hxk : xl ≤ k)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hXL : s.mem.readW (off B 72) 64 = BitVec.ofNat 64 xl)
    (hO : s.mem.readW (off B 80) 64 = off O 0)
    (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) (hsepD : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (hrdX : ∀ i < xl, InRegions (s.rd ++ s.wr) (off X i) 1) (hsepX : ∀ i < xl, ∀ x, ofs B x < Z → off X i ≠ x)
    (ho : Scr s O k) (hsepO : ∀ x, ofs O x < k → Z ≤ ofs B x) (hsepB : ∀ x, ofs B x < Z → k ≤ ofs O x)
    (hP : arr s.mem B w 0 = p) (hp2 : 2 ≤ p) (hodd : p % 2 = 1) (hpk : p < 256 ^ k)
    (hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) = x) (hg : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) = g)
    (hb : bnd s.mem D k L p = b) :
    WP isa dpBody s fun t =>
      (Spec.Rsa.bytesAt t.mem O k = (if (0 < x ∧ x < b) ∧ 1 < g ^ x % p ∧ g ^ x % p < p - 1 then
          Spec.Rsa.i2osp (g ^ x % p) k else List.replicate k 0) ∧
        t.gpr .r3 = BitVec.ofNat 64 (if ¬ (0 < x ∧ x < b) then 2 else if 1 < g ^ x % p ∧ g ^ x % p < p - 1 then 1 else 3) ∧
        ∀ i < 18, word t.mem B (112 + 8 * i) = word s.mem B (112 + 8 * i)) ∧ Keep dpBodyRegs s t := by
  have hs := h.hs
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e8 := slot_eq w 8; have e28 := slot_eq w 28
  have rdQ : L = 3 * k → ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1 := fun hq i hi => by
    rw [off_off']; exact hrdD _ (by omega)
  have sepQ : L = 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x := fun hq i hi => by
    rw [off_off']; exact hsepD _ (by omega)
  have rdG : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1 := fun i hi => by
    rw [off_off']; exact hrdD _ (by omega)
  have sepG : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x := fun i hi => by
    rw [off_off']; exact hsepD _ (by omega)
  unfold dpBody
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
    unfold dpBad
    refine WP.seq (WP.mono (WP.keep [.r27] (Q := fun t => t.gpr .r27 = off O 0 ∧ t.mem = s₁.mem) (by
        prun [g23, (hs.congr k1.wr).ld (d := 80) (n := 8) (by omega),
          show s₁.mem.readW (off B 80) 64 = off O 0 from (hw1 80 (by omega)).trans hO])
      (by decide)) fun s₂ ⟨⟨a27, m2⟩, k2⟩ => ?_)
    have k12 := k1.trans k2
    refine WP.seq (WP.mono (Pub.output_ok (b := false) (hs.congr k12.wr) (ho.congr k12.wr)
      ((k2.gpr .r10 (by decide)).trans a10) ((k12.gpr .r29 (by decide)).trans h.h29)
      ((k2.gpr .r28 (by decide)).trans g28) a27 (by rw [k2.gpr .r26 (by decide), a26, decide_eq_false hv])
      (by omega) (by omega) (by omega) hsepO) fun s₃ ⟨⟨ob, ot, _⟩, k3⟩ => ?_)
    refine WP.mono (li_ok s₃ 2 (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨?_, ?_, fun i hi => ?_⟩,
      ((k12.trans k3).trans kt).mono (by decide)⟩
    · rw [tm, ite_eq_right fun hc => hv hc.1]
      exact Pub.zero_bytes fun i hi => by rw [ob i hi]; rfl
    · rw [t3, ite_eq_left hv]
    · rw [tm]
      refine (Pub.Outside.word_apart (d := 112 + 8 * i) ot hsepB (by omega) (by omega) hs.nowrap).trans ?_
      show Mont.word s₂.mem B _ = _
      rw [m2, hw1 _ (by omega)]
  · -- In range.
    rw [a26, mask_beq_zero, Bool.not_eq_false', decide_eq_true_eq] at hv
    unfold dpGood
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
    refine WP.seq (WP.mono (exOut_ok (O := O) (k := k) (hs.congr k13.wr) (ho.congr k13.wr) r10₃
      ((k13.gpr .r29 (by decide)).trans h.h29) ((k13.gpr .r11 (by decide)).trans h.h11)
      ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans g23))
      ((k3.gpr .r28 (by decide)).trans ((k2.gpr .r28 (by decide)).trans g28)) hw hw' hZ (by omega) (by omega)
      (by show Mont.word s₃.mem B 80 = _; rw [Outside.word b3 (by omega) (by omega), m2]
          exact (hw1 80 (by omega)).trans hO) hsepO
      (by rw [p3]; omega) (by rw [z3, p3]; exact Nat.mod_lt _ (by omega)) (by rw [p3]; exact hpk))
      fun s₄ ⟨⟨ob, o3, m, bm, om⟩, k4⟩ => ?_)
    rw [z3, p3] at ob o3
    refine WP.mono (status_ok s₄ (1 < g ^ x % p ∧ g ^ x % p < p - 1) o3) fun t ⟨⟨t3, tm⟩, kt⟩ =>
      ⟨⟨?_, ?_, fun i hi => ?_⟩, ((k13.trans k4).trans kt).mono (by decide)⟩
    · rw [tm, ob]
      by_cases hc : 1 < g ^ x % p ∧ g ^ x % p < p - 1
      · rw [ite_eq_left hc, ite_eq_left ⟨hv, hc⟩]
      · rw [ite_eq_right hc, ite_eq_right fun h' => hc h'.2]
    · rw [t3]; exact congrArg _ (ite_eq_right (fun h' => h' hv)).symm
    · rw [tm]
      refine (Pub.Outside.word_apart (d := 112 + 8 * i) om hsepB (by omega) (by omega) hs.nowrap).trans ?_
      show Mont.word m B _ = _
      rw [Outside.word bm (by omega) (by omega), Outside.word b3 (by omega) (by omega), m2, hw1 _ (by omega)]

end VG.Proof.Ffdh.PPC64LE.Derive
