module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Rows
import VerifiedGarbage.Proof.Ffdh.CombBitBytes
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
-- separate module: the cached attempt's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # FFDH's comb on PPC64LE: a row's digit

`bit_ok`: bit `k = i + j rows` of x, from its octets, most significant
first. `digit_ok`: the five bits of row `i`'s digit. -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Proof.Bignum.PPC64LE

theorem sign_bit {j l : Nat} (hj : j < 2 ^ 32) (hl : l < 2 ^ 32) :
    (BitVec.ofNat 64 j - BitVec.ofNat 64 l) >>> 63 = BitVec.ofNat 64 (if j < l then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> omega

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_sub' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_mul' (a b : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact (Nat.mul_mod _ _ _).symm

theorem ofNat_add' (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_shl3 {a : Nat} (h : 8 * a < 2 ^ 64) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega)]
  omega

theorem ofNat_shr3 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 3 = BitVec.ofNat 64 (a / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem ofNat_and7 (a : Nat) : BitVec.ofNat 64 a &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_mod_of_dvd _ (by decide)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

theorem ofNat_and1 (a : Nat) : BitVec.ofNat 64 a &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (a % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_mod_of_dvd _ (by decide)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

theorem ofNat_shr1 (a : Nat) (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 1 = BitVec.ofNat 64 (a / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]

/-- The shift loop: `r20 := r20 >> c` for the count `c` in `r18`, from 1. -/
theorem shiftLoop_ok {s : State} {v c : Nat} (hv : v < 2 ^ 64) (hc : 1 ≤ c) (hc' : c < 64)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 v) (h18 : s.gpr .r18 = BitVec.ofNat 64 c) :
    WP isa (.loop (.block [.lsr .d .r20 .r20 1, .subi .r18 .r18 1]) (.nonzero .d .r18)) s fun t =>
      (t.gpr .r20 = BitVec.ofNat 64 (v / 2 ^ c) ∧ t.mem = s.mem) ∧ Keep [.r18, .r20] s t := by
  refine WP.mono (wp_countdown (body := .block [.lsr .d .r20 .r20 1, .subi .r18 .r18 1]) (cnt := .r18) (N := c)
    (by omega) (by omega) (fun i t => (t.gpr .r20 = BitVec.ofNat 64 (v / 2 ^ i) ∧ t.mem = s.mem) ∧ Keep [.r18, .r20] s t)
    (fun i hi t ⟨⟨a20, am⟩, ak⟩ _ => ?_) ⟨⟨by rw [h20, Nat.pow_zero, Nat.div_one], rfl⟩, Keep.refl _ _⟩ h18)
    fun t h => h
  refine WP.mono (WP.keep [.r18, .r20] (Q := fun u => u.gpr .r20 = BitVec.ofNat 64 (v / 2 ^ (i + 1)) ∧
      u.mem = t.mem ∧ u.gpr .r18 = t.gpr .r18 - BitVec.ofNat 64 1) (by
    prun [a20, ofNat_shr1 _ (show v / 2 ^ i < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv),
      Nat.div_div_eq_div_mul, ← Nat.pow_succ]) (by decide))
    fun u ⟨⟨b20, bm, b18⟩, bk⟩ => ⟨⟨⟨b20, bm.trans am⟩, (ak.trans bk).mono (by decide)⟩, b18⟩

/-- The registers `bit` writes. -/
def bitRegs : List Reg := [.r0, .r17, .r18, .r19, .r20]

/-- `bit j`: `r20 :=` bit `k = i + j rows` of x, the `L` octets at `X`
(`r27`), with `i + 1` in `r24`, `rows` in `r21` and `L` in `r28`; 0 from
`8 L` up. -/
theorem bit_ok {s : State} {X : Addr} {xb : List Byte} {i rows j : Nat}
    (h28 : s.gpr .r28 = BitVec.ofNat 64 xb.length) (h24 : s.gpr .r24 = BitVec.ofNat 64 (i + 1))
    (h21 : s.gpr .r21 = BitVec.ofNat 64 rows) (h27 : s.gpr .r27 = X)
    (hrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1)
    (hval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n])
    (hj : j < 5) (hk : i + j * rows < 2 ^ 31) (hL : 8 * xb.length < 2 ^ 31) :
    WP isa (bit j) s fun t =>
      (t.gpr .r20 = BitVec.ofNat 64 (Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2) ∧ t.mem = s.mem) ∧
        Keep bitRegs s t := by
  have hrows : rows * j < 2 ^ 31 := by
    have : j * rows < 2 ^ 31 := by omega
    rwa [Nat.mul_comm] at this
  obtain ⟨k, hk_def⟩ : ∃ k, k = i + j * rows := ⟨_, rfl⟩
  rw [← hk_def] at hk ⊢
  unfold bit
  refine WP.seq (WP.mono (WP.keep [.r0, .r18, .r19] (Q := fun t => t.gpr .r19 = BitVec.ofNat 64 k ∧
      t.gpr .r18 = BitVec.ofNat 64 (if k < 8 * xb.length then 1 else 0) ∧ t.mem = s.mem) (by
    prun [h24, h21, h28, exec_li (show j < 2 ^ 15 by omega), ofNat_sub_one (show 1 ≤ i + 1 by omega) (show i + 1 < 2 ^ 64 by omega),
      Nat.add_sub_cancel, ofNat_mul', ofNat_add', ofNat_shl3 (show 8 * xb.length < 2 ^ 64 by omega)]
    rw [show i + rows * j = k by rw [hk_def, Nat.mul_comm rows j]]
    exact ⟨rfl, sign_bit (by omega) (by omega)⟩) rfl) fun s₁ ⟨⟨a19, a18, m1⟩, k1⟩ => ?_)
  refine WP.ite (decide ¬ k < 8 * xb.length) (by
      rw [eval_zero, a18]; by_cases hc : k < 8 * xb.length <;> simp [hc]) (fun hb => ?_) (fun hb => ?_)
  · -- From `8 L` up: 0.
    have hb' : ¬ k < 8 * xb.length := by simpa using hb
    refine WP.mono (WP.keep [.r20] (Q := fun t => t.gpr .r20 = 0 ∧ t.mem = s₁.mem) (by prun; rfl) (by decide))
      fun t ⟨⟨b20, bm⟩, bk⟩ => ⟨⟨?_, bm.trans m1⟩, (k1.trans bk).mono (by decide)⟩
    rw [b20]
    have hlt : Spec.Rsa.os2ip xb < 2 ^ k :=
      Nat.lt_of_lt_of_le (VG.Proof.Bignum.os2ip_lt xb) (by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt hlt]; rfl
  · have hb' : k < 8 * xb.length := by simpa using hb
    obtain ⟨n, hn⟩ : ∃ n, n = xb.length - 1 - k / 8 := ⟨_, rfl⟩
    have hidx : n < xb.length := by omega
    have hn' : xb.length - k / 8 - 1 = n := by omega
    have h28' : s₁.gpr .r28 = BitVec.ofNat 64 xb.length := (k1.gpr .r28 (by decide)).trans h28
    have a17 : s₁.gpr .r27 = X := (k1.gpr .r27 (by decide)).trans h27
    have l3 : InRegions (s₁.rd ++ s₁.wr) (X + BitVec.ofNat 64 n) 1 := by
      rw [k1.rd, k1.wr]; exact hrd _ hidx
    have v3 : (s₁.mem.read (X + BitVec.ofNat 64 n) 1).setWidth 64 =
        BitVec.ofNat 64 (xb[n]'hidx).toNat := by
      rw [Pub.read1_setWidth, m1]; exact (congrArg (BitVec.setWidth 64) (hval _ hidx)).trans
        (BitVec.ofNat_toNat _ _).symm
    refine WP.seq (WP.mono (WP.keep [.r0, .r17, .r18, .r20] (Q := fun t =>
        t.gpr .r20 = BitVec.ofNat 64 (xb[n]'hidx).toNat ∧
        t.gpr .r18 = BitVec.ofNat 64 (k % 8) ∧ t.mem = s₁.mem) (by
      prun [a17, h28', a19, ofNat_shr3 (show k < 2 ^ 64 by omega),
        ofNat_sub' (show k / 8 ≤ xb.length by omega) (show xb.length < 2 ^ 64 by omega),
        ofNat_sub_one (show 1 ≤ xb.length - k / 8 by omega) (show xb.length - k / 8 < 2 ^ 64 by omega),
        hn', exec_lbz' (show Reg.r17 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), l3, v3, ofNat_and7]) rfl) fun s₂ ⟨⟨b20, b18, m2⟩, k2⟩ => ?_)
    have hbyte : (xb[n]'hidx).toNat < 2 ^ 64 :=
      Nat.lt_trans (xb[n]'hidx).isLt (by decide)
    refine WP.seq (WP.mono (Q := fun (t : State) =>
        (t.gpr .r20 = BitVec.ofNat 64 ((xb[n]'hidx).toNat / 2 ^ (k % 8)) ∧ t.mem = s₂.mem) ∧
          Keep [.r18, .r20] s₂ t)
      (WP.ite (decide (k % 8 = 0)) (by
        rw [eval_zero, b18]; by_cases hc : k % 8 = 0 <;> simp [hc]
        intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact hc this) (fun hc => ?_) (fun hc => ?_))
      fun t ht => ?_)
    · have hc' : k % 8 = 0 := by simpa using hc
      refine WP.mono (WP.keep [] (Q := fun t => t = s₂) (by prun) (by decide)) fun t ⟨ht, _⟩ => ?_
      subst ht
      exact ⟨⟨by rw [b20, hc', Nat.pow_zero, Nat.div_one], rfl⟩, Keep.refl _ _⟩
    · have hc' : k % 8 ≠ 0 := by simpa using hc
      exact shiftLoop_ok hbyte (by omega) (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)) b20 b18
    · obtain ⟨⟨c20, cm⟩, ck⟩ := ht
      refine WP.mono (WP.keep [.r0, .r20] (Q := fun u =>
          u.gpr .r20 = BitVec.ofNat 64 ((xb[n]'hidx).toNat / 2 ^ (k % 8) % 2) ∧ u.mem = t.mem)
        (by prun [c20, ofNat_and1]) (by decide)) fun u ⟨⟨d20, dm⟩, dk⟩ => ⟨⟨?_, by rw [dm, cm, m2, m1]⟩,
          (((k1.trans k2).trans ck).trans dk).mono (by decide)⟩
      rw [d20, CombBitBytes.os2ip_bit xb k hb']
      subst hn; rfl

theorem tooth_bv {acc b j : Nat} (hb : b < 2) (hj : j < 5) (ha : acc < 2 ^ j) :
    BitVec.ofNat 64 acc ||| BitVec.ofNat 64 b <<< j = BitVec.ofNat 64 (acc + 2 ^ j * b) := by
  have h2j : 2 ^ j ≤ 16 := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (show j ≤ 4 by omega)) (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b * 2 ^ j < 2 ^ 64 by
      have : b * 2 ^ j ≤ 1 * 16 := Nat.mul_le_mul (by omega) h2j
      omega),
    Nat.mod_eq_of_lt (show acc + 2 ^ j * b < 2 ^ 64 by
      have : 2 ^ j * b ≤ 16 * 1 := Nat.mul_le_mul h2j (by omega)
      omega),
    Nat.or_comm, Nat.mul_comm b, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]

/-- `tooth j`: `r16 := acc + 2^j` bit `i + j rows` of x, for `acc < 2^j`. -/
theorem tooth_ok {s : State} {X : Addr} {xb : List Byte} {i rows j acc : Nat}
    (h28 : s.gpr .r28 = BitVec.ofNat 64 xb.length) (h24 : s.gpr .r24 = BitVec.ofNat 64 (i + 1))
    (h21 : s.gpr .r21 = BitVec.ofNat 64 rows) (h27 : s.gpr .r27 = X)
    (hrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1)
    (hval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n])
    (hj : j < 5) (hk : i + j * rows < 2 ^ 31) (hL : 8 * xb.length < 2 ^ 31)
    (h16 : s.gpr .r16 = BitVec.ofNat 64 acc) (ha : acc < 2 ^ j) :
    WP isa (tooth j) s fun t =>
      (t.gpr .r16 = BitVec.ofNat 64 (acc + 2 ^ j * (Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2)) ∧
        t.mem = s.mem) ∧ Keep (.r16 :: bitRegs) s t := by
  unfold tooth
  refine WP.seq (WP.mono (bit_ok h28 h24 h21 h27 hrd hval hj hk hL) fun t ⟨⟨a20, m⟩, k⟩ => ?_)
  have h16' : t.gpr .r16 = BitVec.ofNat 64 acc := (k.gpr .r16 (by decide)).trans h16
  have hb : Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2 < 2 := Nat.mod_lt _ (by decide)
  have post : ∀ u : State, (u.gpr .r16 = BitVec.ofNat 64 (acc + 2 ^ j * (Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2)) ∧
      u.mem = t.mem) ∧ Keep [.r16, .r20] t u →
      (u.gpr .r16 = BitVec.ofNat 64 (acc + 2 ^ j * (Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2)) ∧
        u.mem = s.mem) ∧ Keep (.r16 :: bitRegs) s u :=
    fun u ⟨⟨b16, bm⟩, bk⟩ => ⟨⟨b16, bm.trans m⟩, (k.trans bk).mono (by decide)⟩
  by_cases h0 : j = 0
  · subst h0
    have ha0 : acc = 0 := by omega
    subst ha0
    simp only [ite_true, List.nil_append]
    refine WP.mono (WP.keep [.r16, .r20] (Q := fun u =>
        u.gpr .r16 = BitVec.ofNat 64 (0 + 2 ^ 0 * (Spec.Rsa.os2ip xb / 2 ^ (i + 0 * rows) % 2)) ∧ u.mem = t.mem)
      ?_ (by decide)) post
    prun [a20, h16']
    rw [Nat.zero_add, Nat.one_mul]
    exact BitVec.zero_or
  · simp only [h0, ite_false, List.singleton_append]
    refine WP.mono (WP.keep [.r16, .r20] (Q := fun u =>
        u.gpr .r16 = BitVec.ofNat 64 (acc + 2 ^ j * (Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2)) ∧ u.mem = t.mem)
      ?_ rfl) post
    prun [a20, h16', exec_lsl (show j < 64 by omega), tooth_bv hb hj ha]

/-- The comb's digit of row `i`, for `rows` rows: `FixedBaseComb.digit` for
`rows = rows bits`. -/
def combDigit (x i rows : Nat) : Nat :=
  Rsa.FixedBaseComb.bit x i + 2 * Rsa.FixedBaseComb.bit x (i + rows) +
    4 * Rsa.FixedBaseComb.bit x (i + 2 * rows) + 8 * Rsa.FixedBaseComb.bit x (i + 3 * rows) +
    16 * Rsa.FixedBaseComb.bit x (i + 4 * rows)

/-- What `bit` reads: the row (`r24`) and row count (`r21`), and the `L`
octets of x at `X` (`r27`). -/
structure XCtx (s : State) (X : Addr) (xb : List Byte) (i rows : Nat) : Prop where
  h28 : s.gpr .r28 = BitVec.ofNat 64 xb.length
  h24 : s.gpr .r24 = BitVec.ofNat 64 (i + 1)
  h21 : s.gpr .r21 = BitVec.ofNat 64 rows
  h27 : s.gpr .r27 = X
  hrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1
  hval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n]
  hk : i + 4 * rows < 2 ^ 31
  hL : 8 * xb.length < 2 ^ 31

theorem XCtx.keep {s t : State} {X : Addr} {xb : List Byte} {i rows : Nat}
    (h : XCtx s X xb i rows) (hm : t.mem = s.mem) (k : Keep (.r16 :: bitRegs) s t) :
    XCtx t X xb i rows :=
  ⟨(k.gpr .r28 (by decide)).trans h.h28, (k.gpr .r24 (by decide)).trans h.h24,
    (k.gpr .r21 (by decide)).trans h.h21, (k.gpr .r27 (by decide)).trans h.h27,
    fun n hn => by rw [k.rd, k.wr]; exact h.hrd n hn, fun n hn => by rw [hm]; exact h.hval n hn, h.hk, h.hL⟩

theorem XCtx.tooth {s : State} {X : Addr} {xb : List Byte} {i rows j acc : Nat}
    (h : XCtx s X xb i rows) (hj : j < 5) (h16 : s.gpr .r16 = BitVec.ofNat 64 acc) (ha : acc < 2 ^ j) :
    WP isa (tooth j) s fun t =>
      (t.gpr .r16 = BitVec.ofNat 64 (acc + 2 ^ j * Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip xb) (i + j * rows)) ∧
        XCtx t X xb i rows) ∧ t.mem = s.mem ∧ Keep (.r16 :: bitRegs) s t :=
  WP.mono (tooth_ok h.h28 h.h24 h.h21 h.h27 h.hrd h.hval hj
      (by have : j * rows ≤ 4 * rows := Nat.mul_le_mul_right _ (by omega)
          have := h.hk; omega) h.hL h16 ha)
    fun t ⟨⟨a16, am⟩, ak⟩ => ⟨⟨a16, h.keep am ak⟩, am, ak⟩

theorem seqs_teeth : seqs ((List.range 5).map tooth) =
    .seq (tooth 0) (.seq (tooth 1) (.seq (tooth 2) (.seq (tooth 3) (tooth 4)))) := rfl

/-- `digit`: `r26 :=` row `i`'s digit of x. -/
theorem digit_ok {s : State} {X : Addr} {xb : List Byte} {i rows : Nat}
    (h : XCtx s X xb i rows) :
    WP isa digit s fun t =>
      (t.gpr .r26 = BitVec.ofNat 64 (combDigit (Spec.Rsa.os2ip xb) i rows) ∧ t.mem = s.mem) ∧
        Keep (.r26 :: .r16 :: bitRegs) s t := by
  unfold digit
  rw [seqs_teeth]
  have hb := Rsa.FixedBaseComb.bit_lt (Spec.Rsa.os2ip xb)
  refine WP.seq (WP.mono (WP.keep [.r16] (Q := fun t => t.gpr .r16 = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by prun) (by decide)) fun t₀ ⟨⟨a0, m0⟩, k0⟩ => ?_)
  have c0 := h.keep m0 (k0.mono (by decide))
  refine WP.seq (WP.seq ?_)
  refine WP.mono (c0.tooth (j := 0) (by decide) a0 (by decide)) fun t₁ ⟨⟨a1, c1⟩, m1, k1⟩ => ?_
  refine WP.seq (WP.mono (c1.tooth (j := 1) (by decide) a1 (by have := hb (i + 0 * rows); omega))
    fun t₂ ⟨⟨a2, c2⟩, m2, k2⟩ => ?_)
  refine WP.seq (WP.mono (c2.tooth (j := 2) (by decide) a2
    (by have := hb (i + 0 * rows); have := hb (i + 1 * rows); omega))
    fun t₃ ⟨⟨a3, c3⟩, m3, k3⟩ => ?_)
  refine WP.seq (WP.mono (c3.tooth (j := 3) (by decide) a3
    (by have := hb (i + 0 * rows); have := hb (i + 1 * rows); have := hb (i + 2 * rows); omega))
    fun t₄ ⟨⟨a4, c4⟩, m4, k4⟩ => ?_)
  refine WP.mono (c4.tooth (j := 4) (by decide) a4
    (by have := hb (i + 0 * rows); have := hb (i + 1 * rows); have := hb (i + 2 * rows)
        have := hb (i + 3 * rows); omega))
    fun t₅ ⟨⟨a5, c5⟩, m5, k5⟩ => ?_
  have k05 := (((((k0.mono (by decide : ∀ r ∈ [Reg.r16], r ∈ Reg.r16 :: bitRegs)).trans k1).trans k2).trans
    k3).trans k4).trans k5
  have hm : t₅.mem = s.mem := by rw [m5, m4, m3, m2, m1, m0]
  refine WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 =
      BitVec.ofNat 64 (combDigit (Spec.Rsa.os2ip xb) i rows) ∧ t.mem = t₅.mem) ?_ (by decide))
    fun t ⟨⟨t26, tm⟩, tk⟩ => ⟨⟨t26, tm.trans hm⟩, (k05.trans tk).mono (by decide)⟩
  prun [a5]
  unfold combDigit
  simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.add_zero, BitVec.add_zero]

end VG.Proof.Ffdh.PPC64LE.Cached
