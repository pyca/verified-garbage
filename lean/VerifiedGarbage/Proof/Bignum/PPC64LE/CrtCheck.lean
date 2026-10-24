module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.TCB.Code

/-!
# The RSA private-key operation on PPC64LE: the checks

`checkN_ok`: the mask of whether `n` is valid. `checkLt_ok`: the mask of
whether one array is below another, and-ed in.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- Whether a word is zero, as a bit. -/
theorem isZero_bits (v : BitVec 64) :
    (((v >>> 1) ||| (v &&& 1#64)) - 1#64) >>> 63 = BitVec.ofNat 64 (if v = 0 then 1 else 0) := by
  by_cases h : v.toNat ≤ 1
  · rcases (show v = 0 ∨ v = 1 by
      rcases (show v.toNat = 0 ∨ v.toNat = 1 by omega) with h | h
      · exact Or.inl (BitVec.eq_of_toNat_eq h)
      · exact Or.inr (BitVec.eq_of_toNat_eq h)) with rfl | rfl <;> decide
  · have hu1 : 1 ≤ ((v >>> 1) ||| (v &&& 1#64)).toNat := by
      have := Nat.left_le_or (n := (v >>> 1).toNat) (m := (v &&& 1#64).toNat)
      rw [BitVec.toNat_or]
      have : (v >>> 1).toNat = v.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have hu2 : ((v >>> 1) ||| (v &&& 1#64)).toNat < 2 ^ 63 := by
      rw [BitVec.toNat_or]
      apply Nat.or_lt_two_pow
      · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := v.isLt; omega
      · rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hv : v ≠ 0 := fun e => by subst e; simp at h
    simp only [hv, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega

/-- `checkN`: `r26 :=` all ones if the `k` bytes of `n` (at `N`, from the
header) are a valid modulus, else 0. -/
theorem checkN_ok {s : State} {S N : Addr} {Z k : Nat} {nb : List Byte} (hs : Scr s S Z) (hZ : 256 ≤ Z)
    (h23 : s.gpr .r23 = S) (hN : word s.mem S oN = off N 0) (hNL : word s.mem S oNLen = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (off N i) = nb[i]'(by omega)) :
    WP isa checkN s fun t =>
      (t.gpr .r26 = BitVec.ofNat 64 0 -
          BitVec.ofNat 64 (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4, .r6, .r12, .r15, .r16, .r18, .r26] s t := by
  have hnw := hs.nowrap
  unfold checkN
  refine WP.seq (WP.mono (WP.keep [.r12, .r6] (Q := fun t => t.gpr .r12 = off N 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s.mem) ?_ (by decide)) fun s₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  · have hN' : s.mem.readW (off S 8) 64 = off N 0 := hN
    have hNL' : s.mem.readW (off S 16) 64 = BitVec.ofNat 64 k := hNL
    prun [h23, oN, oNLen, hs.ld (show 8 + 8 ≤ Z by omega), hs.ld (show 16 + 8 ≤ Z by omega), hN', hNL']
  refine WP.seq (WP.mono (check_ok (nb := nb) a12 a6 hk hk' hlen (by rw [k1.rd, k1.wr]; exact hrd)
    fun i hi => by rw [m1]; exact hb i hi) fun s₂ ⟨hv, m2, k2⟩ => ?_)
  refine WP.mono (WP.keep [.r3, .r4, .r26] (Q := fun t => t.gpr .r26 = BitVec.ofNat 64 0 -
    ((((s₂.gpr .r0 >>> 1) ||| (s₂.gpr .r0 &&& 1#64)) - 1#64) >>> 63) ∧ t.mem = s₂.mem) ?_ (by decide))
    fun t ⟨⟨t26, tm⟩, k3⟩ => ⟨⟨?_, tm.trans (m2.trans m1)⟩, ((k1.trans k2).trans k3).mono⟩
  · prun
  · rw [t26, isZero_bits]
    by_cases h0 : s₂.gpr .r0 = 0
    · simp only [h0, hv.mp h0, ↓reduceIte]
    · have h1 : ¬ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true := fun h => h0 (hv.mpr h)
      simp only [h0, h1, Bool.false_eq_true, ↓reduceIte]

/-- `cmpLt a m`, with array `a`'s digit `2 w` zero: `r20 :=` all ones if
array `a` is below array `m`, else 0, through array 3; `r10` back to array 0. -/
theorem cmpLt_ok {s : State} {B : Addr} {Z w a m : Nat} (hs : Scr s B Z) (ha : a < 8) (hm : m < 8)
    (ha3 : a ≠ 3) (hm3 : m ≠ 3) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0)) (h21 : s.gpr .r21 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (htop : word s.mem B (slot w a + 8 * w) = 0) :
    WP isa (cmpLt a m) s fun t =>
      (t.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64
          (if Mont.val32 s.mem B (slot w a) (2 * w) < Mont.val32 s.mem B (slot w m) (2 * w) then 1 else 0) ∧
        Mont.Outside B (slot w 3) (8 * w) s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
      Keep [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20] s t := by
  have hnw := hs.nowrap
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sm := Nat.le_trans (slot_le (w := w) hm) hZ
  have s3 := Nat.le_trans (slot_le (w := w) (j := 3) (by decide)) hZ
  have d3a := slot_sep (w := w) (Ne.symm ha3)
  have d3m := slot_sep (w := w) (Ne.symm hm3)
  unfold cmpLt
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) h10 h29 a) fun s₁ ⟨⟨a8, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) 3) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) m) fun s₃ ⟨⟨a10, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w a) (dT := slot w 3) (dM := slot w m)
    (hs.congr k13.wr) ((k3.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans a8))
    ((k3.gpr _ (by decide)).trans a9) a10
    ((k13.gpr _ (by decide)).trans h11) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun s₄ ⟨⟨c, hc, hD, h20⟩, out, k4⟩ => ?_)
  have k14 := k13.trans k4
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₄.mem)
    (by prun [(k14.gpr .r21 (by decide)).trans h21]) (by decide)) fun t ⟨⟨t10, tm⟩, k5⟩ =>
    ⟨⟨?_, by rw [m3, m2, m1] at out; rw [tm]; exact out.mono (Nat.le_refl _) (by omega), t10⟩,
      (k14.trans k5).mono⟩
  rw [k5.gpr .r20 (by decide), h20, m3, m2, m1]
  rw [m3, m2, m1] at hD
  have h0 : Mont.w32 s.mem B (slot w a + 4 * (2 * w)) = 0 := by
    have := Mont.word_eq_w32 s.mem B (slot w a + 8 * w)
    rw [show Mont.word s.mem B (slot w a + 8 * w) = 0 from htop, show (0 : BitVec 64).toNat = 0 from rfl,
      show slot w a + 8 * w = slot w a + 4 * (2 * w) by omega] at this
    omega
  rw [h0]
  have hDl' := Mont.val32_lt s₄.mem B (slot w 3) (2 * w)
  have hAl := Mont.val32_lt s.mem B (slot w a) (2 * w)
  have hMl := Mont.val32_lt s.mem B (slot w m) (2 * w)
  congr 2
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · simp only [Nat.lt_irrefl, ite_false]
    have h : ¬ Mont.val32 s.mem B (slot w a) (2 * w) < Mont.val32 s.mem B (slot w m) (2 * w) := by omega
    simp only [h, ite_false]
  · simp only [Nat.zero_lt_one, ite_true]
    have h : Mont.val32 s.mem B (slot w a) (2 * w) < Mont.val32 s.mem B (slot w m) (2 * w) := by omega
    simp only [h, ite_true]

/-- `checkLt a m`: `r26 &=` `cmpLt a m`'s mask. -/
theorem checkLt_ok {s : State} {B : Addr} {Z w a m : Nat} (hs : Scr s B Z) (ha : a < 8) (hm : m < 8)
    (ha3 : a ≠ 3) (hm3 : m ≠ 3) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0)) (h21 : s.gpr .r21 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (htop : word s.mem B (slot w a + 8 * w) = 0) :
    WP isa (checkLt a m) s fun t =>
      (t.gpr .r26 = s.gpr .r26 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64
          (if Mont.val32 s.mem B (slot w a) (2 * w) < Mont.val32 s.mem B (slot w m) (2 * w) then 1 else 0)) ∧
        Mont.Outside B (slot w 3) (8 * w) s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
      Keep [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20, .r26] s t := by
  unfold checkLt
  refine WP.seq (WP.mono (cmpLt_ok hs ha hm ha3 hm3 hw1 hw' hZ h10 h21 h29 h11 htop)
    fun s₁ ⟨⟨a20, o1, a10⟩, k1⟩ => ?_)
  refine WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 = s₁.gpr .r26 &&& s₁.gpr .r20 ∧ t.mem = s₁.mem)
    (by prun) (by decide)) fun t ⟨⟨t26, tm⟩, k2⟩ =>
    ⟨⟨by rw [t26, a20, k1.gpr .r26 (by decide)], by rw [tm]; exact o1, by rw [k2.gpr .r10 (by decide)]; exact a10⟩,
      (k1.trans k2).mono⟩

/-- Montgomery multiplication modulo `M = R - 1` is exact: `R ≡ 1`. -/
theorem mont_exact {o x R N : Nat} (hN : N + 1 = R) (ho : o < N) (hx : x < N) (h : o * R % N = x % N) :
    o = x := by
  have hR : R % N = 1 % N := by rw [← hN, Nat.add_mod_left]
  rw [Nat.mul_mod, hR, ← Nat.mul_mod, Nat.mul_one, Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt hx] at h
  exact h

/-- Neither below the other: equal. -/
theorem eq_masks (x y : Nat) :
    ((BitVec.ofNat 64 0 - BitVec.ofNat 64 (if x < y then 1 else 0)) |||
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if y < x then 1 else 0))) ^^^ (BitVec.ofNat 64 0 - 1#64) =
      BitVec.ofNat 64 0 - BitVec.ofNat 64 (if x = y then 1 else 0) := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · simp only [h, ↓reduceIte, Nat.lt_asymm h, Nat.ne_of_lt h]; decide
  · subst h; simp only [Nat.lt_irrefl, ↓reduceIte]; decide
  · simp only [h, ↓reduceIte, Nat.lt_asymm h, Nat.ne_of_gt h]; decide

/-- The all-ones word's low digit. -/
theorem w32_ones {m : Mem} {B : Addr} {d : Nat} (h : word m B d = BitVec.allOnes 64) :
    Mont.w32 m B d = 2 ^ 32 - 1 := by
  have := Mont.word_eq_w32 m B d
  rw [show Mont.word m B d = BitVec.allOnes 64 from h, BitVec.toNat_allOnes] at this
  have h1 : Mont.w32 m B d < 2 ^ 32 := BitVec.isLt _
  have h2 : Mont.w32 m B (d + 4) < 2 ^ 32 := BitVec.isLt _
  omega

/-- A word apart from every range that changed. -/
theorem outs_word {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Mont.Outs base rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ fun r hr => by
    have := hd r hr; simp only [Mont.ofs]; rw [show (_ - base).toNat = ofs base _ from rfl, ofs_off base (by omega)]
    omega).symm).symm

/-- The registers `checkPQ` writes. -/
def pqRegs : List Reg :=
  [.r12, .r24, .r26] ++ Pub.montRegs ++ [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20]

/-- `checkPQ`, with `M = 2^(64 w) - 1` in array 0, `n` in array 1 (its digit
`2 w` zero), `p` in array 4 and `q` in array 5, `p q < M`: `r26 &=` all ones
if `p q = n`, else 0, changing only arrays 2, 3 and 6. -/
theorem checkPQ_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0)) (h21 : s.gpr .r21 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hM : Mont.val32 s.mem B (slot w 0) (2 * w) = 2 ^ (64 * w) - 1)
    (hM0 : word s.mem B (slot w 0) = BitVec.allOnes 64)
    (hq : Mont.val32 s.mem B (slot w 5) (2 * w) < 2 ^ (64 * w) - 1)
    (hpq : Mont.val32 s.mem B (slot w 4) (2 * w) * Mont.val32 s.mem B (slot w 5) (2 * w) < 2 ^ (64 * w) - 1)
    (h1top : word s.mem B (slot w 1 + 8 * w) = 0) :
    WP isa checkPQ s fun t =>
      (t.gpr .r26 = s.gpr .r26 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64
          (if Mont.val32 s.mem B (slot w 4) (2 * w) * Mont.val32 s.mem B (slot w 5) (2 * w) =
            Mont.val32 s.mem B (slot w 1) (2 * w) then 1 else 0)) ∧
        Mont.Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem ∧
        t.gpr .r10 = off B (slot w 0)) ∧ Keep pqRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e6 := e 6; have e7 := e 7
  have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hR1 : 1 ≤ 2 ^ (64 * w) := Nat.one_le_two_pow
  unfold checkPQ
  -- `r12 := 1`.
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = 1#64 ∧ t.mem = s.mem) (by prun)
    (by decide)) fun s₁ ⟨⟨a12, m1⟩, k1⟩ => ?_)
  -- `p q` into array 6, exactly.
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 6) (a := 4) (b := 5) (hs.congr k1.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11) (by rw [a12]; decide)
    (by rw [m1, a12, w32_ones hM0]; decide) (by rw [m1, hM]; exact hq)) fun s₂ ⟨⟨h6l, e6v, o2⟩, k2⟩ => ?_)
  rw [m1, hM] at h6l e6v
  have k12 := k1.trans k2
  have hP : Mont.val32 s₂.mem B (slot w 6) (2 * w) =
      Mont.val32 s.mem B (slot w 4) (2 * w) * Mont.val32 s.mem B (slot w 5) (2 * w) := by
    exact mont_exact (by omega) h6l hpq e6v
  have o2' : Mont.Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]
      s.mem s₂.mem := by rw [← m1]; exact o2
  have v21 : Mont.val32 s₂.mem B (slot w 1) (2 * w) = Mont.val32 s.mem B (slot w 1) (2 * w) :=
    o2'.val32 (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                  rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega)
  -- Array 6's word `w` := 0.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 6) fun s₃ ⟨⟨a14, m3⟩, k3⟩ => ?_
  refine WP.mono (WP.keep [.r14, .r0] (Q := fun t =>
    t.mem = s₃.mem.writeW (off B (slot w 6 + 8 * w)) (0 : BitVec 64)) ?_ (by decide)) fun s₄ ⟨m4, k4⟩ => ?_
  · have e16 : off B (slot w 6 + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w 6 + 8 * w) := by
      rw [off, VG.Offset.add_ofNat_sub B (show 16 ≤ slot w 6 + 8 * (w + 2) by omega)]; congr 2
    prun [a14, (k3.gpr .r29 (by decide)).trans ((k12.gpr .r29 (by decide)).trans h29), off_add, e16,
      (hs.congr (k12.trans k3).wr).st (show slot w 6 + 8 * w + 8 ≤ Z by omega)]
    rfl
  have k14 := (k12.trans k3).trans k4
  rw [m3] at m4
  have ow := writeW_outside s₂.mem B (d := slot w 6 + 8 * w) (0 : BitVec 64) (by omega)
  have v46 : Mont.val32 s₄.mem B (slot w 6) (2 * w) =
      Mont.val32 s.mem B (slot w 4) (2 * w) * Mont.val32 s.mem B (slot w 5) (2 * w) := by
    rw [m4, Mont.Outside.val32 (fun x hx => ow x hx) (by omega) (by omega), hP]
  have v41 : Mont.val32 s₄.mem B (slot w 1) (2 * w) = Mont.val32 s.mem B (slot w 1) (2 * w) := by
    rw [m4, Mont.Outside.val32 (fun x hx => ow x hx) (by omega) (by omega), v21]
  have t46 : word s₄.mem B (slot w 6 + 8 * w) = 0 := by rw [m4]; exact word_writeW_self _ _ _ _
  have t41 : word s₄.mem B (slot w 1 + 8 * w) = 0 := by
    rw [m4, ow.word (by omega) (by omega)]
    have hw1 : word s₂.mem B (slot w 1 + 8 * w) = word s.mem B (slot w 1 + 8 * w) := by
      refine outs_word o2' (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega
    rw [hw1]; exact h1top
  -- `p q < n`?
  refine WP.seq (WP.mono (cmpLt_ok (a := 6) (m := 1) (hs.congr k14.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega) hw' hZ ((k14.gpr _ (by decide)).trans h10) ((k14.gpr _ (by decide)).trans h21)
    ((k14.gpr _ (by decide)).trans h29) ((k14.gpr _ (by decide)).trans h11) t46)
    fun s₅ ⟨⟨a20, o5, a10⟩, k5⟩ => ?_)
  rw [v46, v41] at a20
  refine WP.seq (WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = s₅.gpr .r20 ∧ t.mem = s₅.mem)
    (by prun [BitVec.add_zero])
    (by decide)) fun s₆ ⟨⟨a24, m6⟩, k6⟩ => ?_)
  have k16 := (k14.trans k5).trans k6
  -- `n < p q`?
  refine WP.seq (WP.mono (cmpLt_ok (a := 1) (m := 6) (hs.congr k16.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega) hw' hZ (by rw [k6.gpr .r10 (by decide)]; exact a10)
    ((k16.gpr _ (by decide)).trans h21)
    ((k16.gpr _ (by decide)).trans h29) ((k16.gpr _ (by decide)).trans h11)
    (by rw [m6, (show Outside B (slot w 3) (8 * w) s₄.mem s₅.mem from fun x hx => o5 x hx).word (by omega)
      (by omega)]; exact t41))
    fun s₇ ⟨⟨b20, o7, b10⟩, k7⟩ => ?_)
  rw [m6, o5.val32 (by omega) (by omega), o5.val32 (by omega) (by omega), v46, v41] at b20
  refine WP.mono (WP.keep [.r0, .r3, .r26] (Q := fun t => t.gpr .r26 = s₇.gpr .r26 &&&
    ((s₇.gpr .r24 ||| s₇.gpr .r20) ^^^ (BitVec.ofNat 64 0 - 1#64)) ∧ t.mem = s₇.mem) (by prun) (by decide))
    fun t ⟨⟨t26, tm⟩, k8⟩ => ⟨⟨?_, ?_, by rw [k8.gpr .r10 (by decide)]; exact b10⟩, ?_⟩
  · rw [t26, b20, k7.gpr .r24 (by decide), a24, a20, eq_masks, k7.gpr .r26 (by decide),
      k16.gpr .r26 (by decide)]
  · intro x hx
    rw [tm]
    have hx3 : Mont.ofs B x < slot w 3 ∨ slot w 3 + 8 * w ≤ Mont.ofs B x := by
      have := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)); simp only at this; omega
    have hx6 : Mont.ofs B x < slot w 6 + 8 * w ∨ slot w 6 + 8 * w + 8 ≤ Mont.ofs B x := by
      have := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      simp only at this; omega
    rw [o7 x hx3, m6, o5 x hx3, m4, ow x (by simp only [Mont.ofs, ofs] at hx6 ⊢; omega)]
    exact o2' x hx
  · exact (k16.trans (k7.trans k8)).mono

end VG.Proof.Bignum.PPC64LE.Crt
