module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Rows
import VerifiedGarbage.Proof.Ffdh.CombBitBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

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
(the header's word 8), with `i + 1` and `rows` in the header and `L` in
`r28`; 0 from `8 L` up. -/
theorem bit_ok {s : State} {B X : Addr} {Z : Nat} {xb : List Byte} {i rows j : Nat} (hs : Scr s B Z)
    (hZ : 72 ≤ Z) (h23 : s.gpr .r23 = B) (h28 : s.gpr .r28 = BitVec.ofNat 64 xb.length)
    (hIw : s.mem.readW (off B hI) 64 = BitVec.ofNat 64 (i + 1))
    (hRw : s.mem.readW (off B hRows) 64 = BitVec.ofNat 64 rows) (hX : s.mem.readW (off B 64) 64 = X)
    (hrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1)
    (hval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n])
    (hj : j < 5) (hk : i + j * rows < 2 ^ 31) (hL : 8 * xb.length < 2 ^ 31) :
    WP isa (bit j) s fun t =>
      (t.gpr .r20 = BitVec.ofNat 64 (Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2) ∧ t.mem = s.mem) ∧
        Keep bitRegs s t := by
  have hrows : rows * j < 2 ^ 31 := by
    have : j * rows < 2 ^ 31 := by omega
    rwa [Nat.mul_comm] at this
  have l0 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 32) 8 := by
    rw [h23]; exact hs.ld (d := 32) (n := 8) (by omega)
  have l1 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 24) 8 := by
    rw [h23]; exact hs.ld (d := 24) (n := 8) (by omega)
  have v0 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (i + 1) := by rw [h23]; exact hIw
  have v1 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 rows := by rw [h23]; exact hRw
  obtain ⟨k, hk_def⟩ : ∃ k, k = i + j * rows := ⟨_, rfl⟩
  rw [← hk_def] at hk ⊢
  unfold bit
  refine WP.seq (WP.mono (WP.keep [.r0, .r18, .r19] (Q := fun t => t.gpr .r19 = BitVec.ofNat 64 k ∧
      t.gpr .r18 = BitVec.ofNat 64 (if k < 8 * xb.length then 1 else 0) ∧ t.mem = s.mem) (by
    unfold ldh
    prun [hI, hRows, l0, l1, v0, v1, h28, exec_li (show j < 2 ^ 15 by omega), ofNat_sub_one (show 1 ≤ i + 1 by omega) (show i + 1 < 2 ^ 64 by omega),
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
    have l2 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r23 + BitVec.ofNat 64 64) 8 := by
      rw [k1.rd, k1.wr, k1.gpr .r23 (by decide), h23]; exact hs.ld (d := 64) (n := 8) (by omega)
    have v2 : s₁.mem.readW (s₁.gpr .r23 + BitVec.ofNat 64 64) 64 = X := by
      rw [m1, k1.gpr .r23 (by decide), h23]; exact hX
    have h28' : s₁.gpr .r28 = BitVec.ofNat 64 xb.length := (k1.gpr .r28 (by decide)).trans h28
    have l3 : InRegions (s₁.rd ++ s₁.wr) (X + BitVec.ofNat 64 n) 1 := by
      rw [k1.rd, k1.wr]; exact hrd _ hidx
    have v3 : (s₁.mem.read (X + BitVec.ofNat 64 n) 1).setWidth 64 =
        BitVec.ofNat 64 (xb[n]'hidx).toNat := by
      rw [Pub.read1_setWidth, m1]; exact (congrArg (BitVec.setWidth 64) (hval _ hidx)).trans
        (BitVec.ofNat_toNat _ _).symm
    refine WP.seq (WP.mono (WP.keep [.r0, .r17, .r18, .r20] (Q := fun t =>
        t.gpr .r20 = BitVec.ofNat 64 (xb[n]'hidx).toNat ∧
        t.gpr .r18 = BitVec.ofNat 64 (k % 8) ∧ t.mem = s₁.mem) (by
      prun [l2, v2, h28', a19, ofNat_shr3 (show k < 2 ^ 64 by omega),
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

end VG.Proof.Ffdh.PPC64LE.Cached
