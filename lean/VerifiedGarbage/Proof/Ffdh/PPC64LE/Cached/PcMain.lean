module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcTable
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scalar
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scan
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
-- separate module: the precompute's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # FFDH's context on PPC64LE: the width

`boundBits_ok`: the bound's bit length, from its first nonzero octet;
`width_ok`: the recognized width if it is below it. -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Precompute
open VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.PPC64LE.GenerateKey (bptr boundPtr_ok scan_ok scanRegs bptr_bnd)
open VG.Spec.RsaKeyGen (bitLength)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)

theorem shr3_ofNat {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 3 = BitVec.ofNat 64 (x / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx]
  omega

theorem bitLength_pos {b : Nat} (hb : b ≠ 0) : 1 ≤ bitLength b := by
  unfold bitLength; simp only [hb, ↓reduceIte]; omega

/-- `b / 2^i` is not zero below `b`'s bit length, and zero at it. -/
theorem div_pow_bits {b i : Nat} (hb : b ≠ 0) :
    (b / 2 ^ i = 0 ↔ bitLength b ≤ i) := by
  have hbl := VG.Proof.Ffdh.KeyScalar.bitLength_bounds hb
  rw [Nat.div_eq_zero_iff_lt (Nat.two_pow_pos i)]
  constructor
  · intro h
    by_contra hc
    have : 2 ^ i ≤ 2 ^ (bitLength b - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · intro h
    exact Nat.lt_of_lt_of_le hbl.2 (Nat.pow_le_pow_right (by decide) h)

/-- The bit-length loop: `r15 :=` the bit length of the nonzero octet in
`r14`. -/
theorem bitLoop_ok {s : State} {b : Nat} (hb : b ≠ 0) (hb' : b < 256)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 b) (h15 : s.gpr .r15 = BitVec.ofNat 64 0) :
    WP isa (.loop (.block [.lsr .d .r14 .r14 1, .addi .r15 .r15 1]) (.nonzero .d .r14)) s fun t =>
      (t.gpr .r15 = BitVec.ofNat 64 (bitLength b) ∧ t.mem = s.mem) ∧ Keep [.r14, .r15] s t := by
  have hbl : bitLength b ≤ 8 := by
    have := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds hb).1
    by_contra hc
    have : 2 ^ 8 ≤ 2 ^ (bitLength b - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  refine WP.loop (M := isa) (fun (n : Nat) (t : State) => ∃ i, n = bitLength b - i ∧ i < bitLength b ∧
      t.gpr .r14 = BitVec.ofNat 64 (b / 2 ^ i) ∧ t.gpr .r15 = BitVec.ofNat 64 i ∧ t.mem = s.mem ∧
      Keep [.r14, .r15] s t)
    (fun n t ⟨i, hn, hi, t14, t15, tm, kt⟩ => ?_) _ s ⟨0, rfl, bitLength_pos hb, by rw [h14]; simp, h15, rfl,
      Keep.refl _ _⟩
  refine WP.mono (WP.keep [.r14, .r15] (Q := fun u => u.gpr .r14 = BitVec.ofNat 64 (b / 2 ^ (i + 1)) ∧
      u.gpr .r15 = BitVec.ofNat 64 (i + 1) ∧ u.mem = t.mem) (by
    prun [t14, t15, ofNat_shr1 _ (show b / 2 ^ i < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
      Nat.div_div_eq_div_mul, ← Nat.pow_succ, BitVec.ofNat_add]) (by decide)) fun u ⟨⟨u14, u15, um⟩, ku⟩ => ?_
  have hv : b / 2 ^ (i + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hz := div_pow_bits (i := i + 1) hb
  by_cases hi' : i + 1 = bitLength b
  · refine Or.inl ⟨(VG.Proof.Bignum.PPC64LE.eval_nonzero u .r14).trans (by
        rw [u14, show b / 2 ^ (i + 1) = 0 from hz.mpr (by omega)]; rfl),
      ⟨by rw [u15, hi'], um.trans tm⟩, (kt.trans ku).mono (by decide)⟩
  · have hne : b / 2 ^ (i + 1) ≠ 0 := fun e => by have := hz.mp e; omega
    refine Or.inr ⟨(VG.Proof.Bignum.PPC64LE.eval_nonzero u .r14).trans (by
        rw [u14, show (BitVec.ofNat 64 (b / 2 ^ (i + 1)) != 0) = true from by
          simp only [bne_iff_ne, ne_eq]
          intro e
          have := congrArg BitVec.toNat e
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at this
          exact hne this]), _, by omega, i + 1, rfl, by omega, u14, u15, um.trans tm,
      (kt.trans ku).mono (by decide)⟩

/-- The bound's lead octet. -/
abbrev leadOct (bd : List Byte) : Nat := (bd.getD (VG.Proof.Ffdh.lead bd) 0).toNat

/-- The registers `boundBits` writes. -/
def bbRegs : List Reg := scanRegs ++ [.r0, .r12, .r14, .r15, .r16]

/-- `boundBits`: `r16 :=` the bit length of the bound's `k` octets (q's, or p's
without q), from its first nonzero octet. -/
theorem boundBits_ok {s : State} {D : Addr} {k L : Nat} (h21 : s.gpr .r21 = D)
    (h27 : s.gpr .r27 = BitVec.ofNat 64 L) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hL : L = 2 * k ∨ L = 3 * k)
    (hk : 1 ≤ k) (hk32 : k < 2 ^ 32) (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hlead : leadOct (VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L)) ≠ 0) :
    WP isa boundBits s fun t =>
      (t.gpr .r16 = BitVec.ofNat 64 (8 * (k - VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd k
          (Spec.Rsa.bytesAt s.mem D L)) - 1) + bitLength (leadOct (VG.Proof.Ffdh.KeyScalar.bnd k
            (Spec.Rsa.bytesAt s.mem D L)))) ∧ t.mem = s.mem) ∧ Keep bbRegs s t := by
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length (dom := Spec.Rsa.bytesAt s.mem D L) (k := k)
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hL)
  have hne : VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L) ≠ [] := fun he => by
    rw [he] at hbl; simp at hbl; omega
  have hld := VG.Proof.Ffdh.lead_lt hne
  rw [hbl] at hld
  generalize hbd : VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L) = bd at hlead hne hld ⊢
  unfold boundBits
  refine WP.seq (WP.mono (boundPtr_ok h21 h27 h28 (by omega) hk32) fun s₁ ⟨⟨a12, m1⟩, k1⟩ => ?_)
  have hbytes : Spec.Rsa.bytesAt s₁.mem (bptr D k L) k = bd := by rw [m1, bptr_bnd _ _ hL, hbd]
  have hrdP : ∀ i < k, InRegions (s₁.rd ++ s₁.wr) (off (bptr D k L) i) 1 := fun i hi => by
    rw [k1.rd, k1.wr]
    unfold bptr
    split
    · rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact hrd _ (by omega)
    · exact hrd _ (by omega)
  refine WP.seq (WP.mono (scan_ok hk hk32 hrdP a12 ((k1.gpr .r28 (by decide)).trans h28))
    fun u hu => WP.seq (WP.mono hu fun s₂ ⟨⟨a22, a14, m2⟩, k2⟩ => ?_))
  rw [hbytes] at a22 a14
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = BitVec.ofNat 64 0 ∧ t.mem = s₂.mem)
    (by prun) (by decide)) fun s₃ ⟨⟨a15, m3⟩, k3⟩ => ?_)
  have hb256 : leadOct bd < 256 := (bd.getD (VG.Proof.Ffdh.lead bd) 0).isLt
  refine WP.seq (WP.mono (bitLoop_ok (b := leadOct bd) hlead hb256 (by
      rw [k3.gpr .r14 (by decide), a14]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      try omega) a15) fun s₄ ⟨⟨a15', m4⟩, k4⟩ => ?_)
  have k14 := (k12.trans k3).trans k4
  have hb8 : bitLength (leadOct bd) ≤ 8 := by
    have := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds hlead).1
    by_contra hc
    have : 2 ^ 8 ≤ 2 ^ (bitLength (leadOct bd) - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have g28 : s₄.gpr .r28 = BitVec.ofNat 64 k := (k14.gpr .r28 (by decide)).trans h28
  have g22 : s₄.gpr .r22 = BitVec.ofNat 64 (VG.Proof.Ffdh.lead bd) := by
    rw [k4.gpr .r22 (by decide), k3.gpr .r22 (by decide), a22]
  refine WP.mono (WP.keep [.r16] (Q := fun t => t.gpr .r16 = BitVec.ofNat 64 (8 * (k - VG.Proof.Ffdh.lead bd - 1) +
      bitLength (leadOct bd)) ∧ t.mem = s₄.mem) (by
    prun [g28, g22, a15', ofNat_sub' (show VG.Proof.Ffdh.lead bd ≤ k by omega) (show k < 2 ^ 64 by omega),
      ofNat_shl3 (show 8 * (k - VG.Proof.Ffdh.lead bd) < 2 ^ 64 by omega),
      ofNat_sub' (show 8 ≤ 8 * (k - VG.Proof.Ffdh.lead bd) by omega) (show 8 * (k - VG.Proof.Ffdh.lead bd) < 2 ^ 64 by omega),
      ← BitVec.ofNat_add]
    congr 1; omega) (by decide)) fun t ⟨⟨a16, mt⟩, kt⟩ => ?_
  exact ⟨⟨a16, by rw [mt, m4, m3, m2, m1]⟩, (k14.trans kt).mono (by decide)⟩

/-! ## The width -/

theorem lt_bit {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split <;> omega

theorem pos_bit {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ((BitVec.ofNat 64 0 - (BitVec.ofNat 64 a - BitVec.ofNat 64 b)) >>> 63 != 0) = decide (b < a) := by
  have e : (BitVec.ofNat 64 0 - (BitVec.ofNat 64 a - BitVec.ofNat 64 b)) >>> 63 =
      BitVec.ofNat 64 (if b < a then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    split <;> omega
  rw [e]; split <;> simp_all

/-- The width: the recognized one `cap` if it is not zero and below the
bound's bit length `bl`, else `bl`. -/
abbrev widthOf (cap bl : Nat) : Nat := if cap ≠ 0 ∧ cap < bl then cap else bl

/-- `width`: `r16 := widthOf cap bl`, `cap` in the header's word 12. -/
theorem width_ok {s : State} {S : Addr} {Z cap bl : Nat} (hs : Scr s S Z) (hZ : 104 ≤ Z) (h23 : s.gpr .r23 = S)
    (hcap : s.mem.readW (off S hCap) 64 = BitVec.ofNat 64 cap) (h16 : s.gpr .r16 = BitVec.ofNat 64 bl)
    (hc : cap < 2 ^ 32) (hb : bl < 2 ^ 32) :
    WP isa width s fun t => (t.gpr .r16 = BitVec.ofNat 64 (widthOf cap bl) ∧ t.mem = s.mem) ∧
      Keep [.r8, .r9, .r16] s t := by
  have l96 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 96) 8 := by
    rw [h23]; exact hs.ld (d := 96) (n := 8) (by omega)
  have v96 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 96) 64 = BitVec.ofNat 64 cap := by rw [h23]; exact hcap
  unfold width
  refine WP.seq (WP.mono (WP.keep [.r8, .r9] (Q := fun t => t.gpr .r8 = BitVec.ofNat 64 cap ∧
      t.gpr .r9 = BitVec.ofNat 64 (if cap < bl then 1 else 0) ∧ t.mem = s.mem) (by
    unfold ldh
    prun [hCap, l96, v96, h16, lt_bit hc hb]) (by decide)) fun s₁ ⟨⟨a8, a9, m1⟩, k1⟩ => ?_)
  have g16 : s₁.gpr .r16 = BitVec.ofNat 64 bl := (k1.gpr .r16 (by decide)).trans h16
  refine WP.ite (decide (cap = 0)) (eval_zero_ofNat _ _ (by omega) a8) (fun hz => ?_) (fun hz => ?_)
  · have hz' : cap = 0 := by simpa using hz
    refine WP.mono (WP.keep [] (Q := fun t => t = s₁) (by prun) (by decide)) fun t ⟨ht, _⟩ => ?_
    subst ht
    exact ⟨⟨by rw [g16]; simp [widthOf, hz'], m1⟩, k1.mono (by decide)⟩
  · have hz' : cap ≠ 0 := by simpa using hz
    refine WP.ite (decide (¬ cap < bl)) ((eval_zero_ofNat _ _ (by split <;> omega) a9).trans (by
      split <;> simp_all)) (fun hl => ?_) (fun hl => ?_)
    · have hl' : ¬ cap < bl := by simpa using hl
      refine WP.mono (WP.keep [] (Q := fun t => t = s₁) (by prun) (by decide)) fun t ⟨ht, _⟩ => ?_
      subst ht
      exact ⟨⟨by rw [g16]; simp [widthOf, hl'], m1⟩, k1.mono (by decide)⟩
    · have hl' : cap < bl := by simpa using hl
      refine WP.mono (WP.keep [.r16] (Q := fun t => t.gpr .r16 = BitVec.ofNat 64 cap ∧ t.mem = s₁.mem)
        (by prun [a8, BitVec.add_zero]) (by decide)) fun t ⟨⟨t16, tm⟩, kt⟩ => ?_
      exact ⟨⟨by rw [t16]; simp [widthOf, hz', hl'], tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩

/-! ## The metadata -/

/-- `rows`: `r18 := ⌈bits / 5⌉`, at least 1. -/
theorem rowsLoop_ok {s : State} {bits : Nat} (hb1 : 1 ≤ bits) (hb : bits < 2 ^ 31)
    (h16 : s.gpr .r16 = BitVec.ofNat 64 bits) :
    WP isa rows s fun t => (t.gpr .r18 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧ t.mem = s.mem) ∧
      Keep [.r0, .r18, .r19] s t := by
  unfold rows
  refine WP.seq (WP.mono (WP.keep [.r18, .r19] (Q := fun t => t.gpr .r19 = BitVec.ofNat 64 bits - BitVec.ofNat 64 0 ∧
      t.gpr .r18 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by prun [h16, BitVec.add_zero]; exact (BitVec.sub_zero _).symm)
    (by decide))
    fun s₁ ⟨⟨a19, a18, m1⟩, k1⟩ => ?_)
  refine WP.loop (M := isa) (fun (n : Nat) (t : State) => ∃ i, n = bits - 5 * i ∧ 5 * i < bits ∧
      t.gpr .r19 = BitVec.ofNat 64 bits - BitVec.ofNat 64 (5 * i) ∧ t.gpr .r18 = BitVec.ofNat 64 i ∧
      t.mem = s.mem ∧ Keep [.r0, .r18, .r19] s t)
    (fun n t ⟨i, hn, hi, t19, t18, tm, kt⟩ => ?_) _ s₁ ⟨0, rfl, by omega, a19, a18, m1, k1.mono (by decide)⟩
  refine WP.mono (WP.keep [.r0, .r18, .r19] (Q := fun u =>
      u.gpr .r19 = BitVec.ofNat 64 bits - BitVec.ofNat 64 (5 * (i + 1)) ∧ u.gpr .r18 = BitVec.ofNat 64 (i + 1) ∧
      u.gpr .r0 = (BitVec.ofNat 64 0 - (BitVec.ofNat 64 bits - BitVec.ofNat 64 (5 * (i + 1)))) >>> 63 ∧
      u.mem = t.mem) (by
    have e : BitVec.ofNat 64 bits - BitVec.ofNat 64 (5 * i) - BitVec.ofNat 64 5 =
        BitVec.ofNat 64 bits - BitVec.ofNat 64 (5 * (i + 1)) := by
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]; congr 2
    prun [t19, t18, e, BitVec.ofNat_add]) (by decide)) fun u ⟨⟨u19, u18, u0, um⟩, ku⟩ => ?_
  have hc := pos_bit (a := bits) (b := 5 * (i + 1)) (by omega) (by omega)
  by_cases hx : 5 * (i + 1) < bits
  · refine Or.inr ⟨(VG.Proof.Bignum.PPC64LE.eval_nonzero u .r0).trans (by rw [u0, hc]; simp [hx]), _, by omega,
      i + 1, rfl, hx, u19, u18, um.trans tm, (kt.trans ku).mono (by decide)⟩
  · refine Or.inl ⟨(VG.Proof.Bignum.PPC64LE.eval_nonzero u .r0).trans (by rw [u0, hc]; simp [hx]),
      ⟨by rw [u18]; congr 1; simp only [Spec.Rsa.FixedBaseComb.rows, Spec.Rsa.FixedBaseComb.teeth]; omega,
        um.trans tm⟩, (kt.trans ku).mono (by decide)⟩

/-- `metadata`: the width, its bytes and the rows to the context's words 0–2
(its address from the header into `r30`), the rows into `r24`. -/
theorem metadata_ok {s : State} {S C : Addr} {Z bits : Nat} (hs : Scr s S Z) (hZ : 8 ≤ Z) (h23 : s.gpr .r23 = S)
    (hC : s.mem.readW (off S hCtx) 64 = C) (hc : Scr s C 24) (h16 : s.gpr .r16 = BitVec.ofNat 64 bits)
    (hb1 : 1 ≤ bits) (hb : bits ≤ 8192) :
    WP isa metadata s fun t =>
      (t.gpr .r30 = C ∧ t.gpr .r24 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
        word t.mem C 0 = BitVec.ofNat 64 bits ∧ word t.mem C 8 = BitVec.ofNat 64 ((bits + 7) / 8) ∧
        word t.mem C 16 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧ Outside C 0 24 s.mem t.mem) ∧
      Keep [.r0, .r17, .r18, .r19, .r24, .r30] s t := by
  unfold metadata
  refine WP.seq (WP.mono (WP.keep [.r17] (Q := fun t => t.gpr .r17 = BitVec.ofNat 64 ((bits + 7) / 8) ∧ t.mem = s.mem)
    (by prun [h16, ← BitVec.ofNat_add, shr3_ofNat (show bits + 7 < 2 ^ 64 by omega)]) (by decide))
    fun s₁ ⟨⟨a17, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (rowsLoop_ok hb1 (by omega) ((k1.gpr .r16 (by decide)).trans h16))
    fun s₂ ⟨⟨a18, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have g23 : s₂.gpr .r23 = S := (k12.gpr .r23 (by decide)).trans h23
  have l0 : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r23 + BitVec.ofNat 64 0) 8 := by
    rw [g23, k12.rd, k12.wr]; exact hs.ld (d := 0) (n := 8) (by omega)
  have v0 : s₂.mem.readW (s₂.gpr .r23 + BitVec.ofNat 64 0) 64 = C := by rw [g23, m2, m1]; exact hC
  have i0 : InRegions s₂.wr (C + BitVec.ofNat 64 0) 8 := by rw [k12.wr]; exact hc.st (d := 0) (n := 8) (by omega)
  have i1 : InRegions s₂.wr (C + BitVec.ofNat 64 8) 8 := by rw [k12.wr]; exact hc.st (d := 8) (n := 8) (by omega)
  have i2 : InRegions s₂.wr (C + BitVec.ofNat 64 16) 8 := by rw [k12.wr]; exact hc.st (d := 16) (n := 8) (by omega)
  have g16 : s₂.gpr .r16 = BitVec.ofNat 64 bits := (k12.gpr .r16 (by decide)).trans h16
  have g17 : s₂.gpr .r17 = BitVec.ofNat 64 ((bits + 7) / 8) := (k2.gpr .r17 (by decide)).trans a17
  refine WP.mono (WP.keep [.r24, .r30] (Q := fun t => t.gpr .r30 = C ∧
      t.gpr .r24 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
      t.mem = ((s₂.mem.writeW (off C 0) (BitVec.ofNat 64 bits)).writeW (off C 8)
        (BitVec.ofNat 64 ((bits + 7) / 8))).writeW (off C 16) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)))
    (by unfold ldh; prun [hCtx, l0, v0, i0, i1, i2, g16, g17, a18, off]; exact BitVec.add_zero _) (by decide))
    fun t ⟨⟨a30, a24, mt⟩, kt⟩ => ?_
  have o0 := writeW_outside s₂.mem C (d := 0) (BitVec.ofNat 64 bits) (by omega)
  have o1 := writeW_outside (s₂.mem.writeW (off C 0) (BitVec.ofNat 64 bits)) C (d := 8)
    (BitVec.ofNat 64 ((bits + 7) / 8)) (by omega)
  have o2 := writeW_outside ((s₂.mem.writeW (off C 0) (BitVec.ofNat 64 bits)).writeW (off C 8)
    (BitVec.ofNat 64 ((bits + 7) / 8))) C (d := 16) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)) (by omega)
  refine ⟨⟨a30, a24, ?_, ?_, ?_, ?_⟩, (k12.trans kt).mono (by decide)⟩
  · rw [mt, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]; exact word_writeW_self _ _ _ _
  · rw [mt, o2.word (by omega) (by omega)]; exact word_writeW_self _ _ _ _
  · rw [mt]; exact word_writeW_self _ _ _ _
  · rw [mt, ← m1, ← m2]
    exact ((o0.mono (by omega) (by omega)).trans (o1.mono (by omega) (by omega))).trans (o2.mono (by omega) (by omega))

/-- `montgomery`: `R² mod p` into array 1 and the inverse into `r12`. -/
theorem montgomery_ok {s : State} {B : Addr} {Z w P : Nat} (h : Env s B Z w) (hp : arr s.mem B w 0 = P)
    (hP : 2 ≤ P) (hodd : (word s.mem B (slot w 0)).toNat % 2 = 1) :
    WP isa montgomery s fun t =>
      (arr t.mem B w 1 = 2 ^ (128 * w) % P ∧ (t.gpr .r12).toNat < 2 ^ 32 ∧
        (w32 t.mem B (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 ∧
        Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧
      Keep [.r0, .r3, .r4, .r5, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r20] s t := by
  have hZ := h.hZ; have hw := h.hw; have hw' := h.hw'
  unfold montgomery
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r5) (by decide) (by decide) 1) fun t₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono ((h.keep k1 (by decide)).base (rd := .r8) (by decide) (by decide) 2) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  refine WP.mono (((h.keep k1 (by decide)).keep k2 (by decide)).base (rd := .r9) (by decide) (by decide) 3)
    fun t₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have e3 := h.keep k13 (by decide)
  have hm : t₃.mem = s.mem := by rw [m3, m2, m1]
  refine WP.seq (WP.mono (r2_ok e3.hs ((k3.gpr .r8 (by decide)).trans a8) a9 e3.h10 ((k3.gpr .r5 (by decide)).trans ((k2.gpr .r5 (by decide)).trans a5))
    e3.h11 (by omega) (by omega) (Nat.le_trans (slot_mono (by decide)) hZ)
    (by rw [hm, ← arr, hp]; exact hP)) fun t₄ ⟨v4, o4, k4⟩ => ?_)
  rw [hm] at v4 o4
  have e4 := e3.keep k4 (by decide)
  have hodd4 : (word t₄.mem B (slot w 0)).toNat % 2 = 1 := by
    rw [o4.word (Or.inl (by simp only [slot, hdrBytes]; omega)) (by have := h.hs.nowrap; simp only [slot, hdrBytes] at hZ ⊢; omega)]
    exact hodd
  refine WP.mono (Pub.minv_ok e4.hs e4.h10 (by simp only [slot, hdrBytes] at hZ ⊢; omega) hodd4)
    fun t ⟨⟨r12a, r12b, mt⟩, kt⟩ => ⟨⟨by rw [arr, mt, v4, ← arr, hp], r12a, by rw [mt]; exact r12b, by rw [mt]; exact o4⟩,
      ((k13.trans k4).trans kt).mono (by decide)⟩

/-! ## The context's words -/

theorem precomputedWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth,
    Spec.Rsa.modulusWords]
  omega

/-- Word `q` of a row holding `x`. -/
theorem row_word {m : Mem} {C : Addr} {w j q x : Nat} (hq : q < w) (hv : rowv m C w j = x) :
    m.readW (C + BitVec.ofNat 64 (8 * (3 + (j * w + q)))) 64 = BitVec.ofNat 64 (x / 2 ^ (64 * q)) := by
  have e := VG.Proof.Bignum.word_of_wv m C (rowOff w j) w hq
  rw [← VG.Proof.Bignum.PPC64LE.Pre.val32_eq_wv] at e
  rw [show 8 * (3 + (j * w + q)) = rowOff w j + 8 * q by unfold rowOff; rw [Nat.mul_comm w j]; omega]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  show (VG.Proof.Bignum.word m C (rowOff w j + 8 * q)).toNat = _
  rw [e]
  have hv' : val32 m C (rowOff w j) (2 * w) = x := hv
  rw [hv']

theorem toWords_get? {x w q : Nat} (hq : q < w) :
    (Spec.Rsa.toWords x w)[q]? = some (BitVec.ofNat 64 (x / 2 ^ (64 * q))) := by
  simp [Spec.Rsa.toWords, hq]

/-- The context's words from its metadata, its prefix rows and its entries. -/
theorem ctx_words {m : Mem} {C : Addr} {k : Nat} {dom : List Byte} (hk : 1 ≤ k)
    (h0 : m.readW (C + BitVec.ofNat 64 0) 64 =
      BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)))
    (h8 : m.readW (C + BitVec.ofNat 64 8) 64 =
      BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) + 7) / 8))
    (h16 : m.readW (C + BitVec.ofNat 64 16) 64 =
      BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom))))
    (hp : rowv m C ((k + 7) / 8) 0 = (Spec.Ffdh.domainOf k dom).p)
    (hr : rowv m C ((k + 7) / 8) 1 = 2 ^ (128 * ((k + 7) / 8)) % (Spec.Ffdh.domainOf k dom).p)
    (he : Ents m C (Spec.Ffdh.domainOf k dom).g (Spec.Ffdh.domainOf k dom).p ((k + 7) / 8)
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)) 32) :
    Spec.Rsa.wordsAt m C (3 + 34 * ((k + 7) / 8)) = VG.Proof.Ffdh.generationValues k dom := by
  generalize hw : (k + 7) / 8 = w at hp hr he ⊢
  have hw1 : 1 ≤ w := by omega
  have hlen : (VG.Proof.Ffdh.generationValues k dom).length = 3 + 34 * w := by
    rw [VG.Proof.Ffdh.generationValues_length, precomputedWords_eq, hw]
  apply List.ext_getElem? fun i => ?_
  by_cases hi : i < 3 + 34 * w
  · have lhs : (Spec.Rsa.wordsAt m C (3 + 34 * w))[i]? = some (m.readW (C + BitVec.ofNat 64 (8 * i)) 64) := by
      simp [Spec.Rsa.wordsAt, hi]
    rw [lhs]
    by_cases hi3 : i < 3
    · have e := VG.Proof.Ffdh.generationValues_headers k dom
      have e' := congrArg (fun l => l[i]?) e
      simp only [List.getElem?_take, hi3, ↓reduceIte] at e'
      rw [e']
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · simpa using h0
      · simpa using h8
      · simpa using h16
    · obtain ⟨i', rfl⟩ : ∃ i', i = 3 + i' := ⟨i - 3, by omega⟩
      have hq : i' % w < w := Nat.mod_lt _ (by omega)
      have hj : i' / w < 34 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
      have hi' : i' = i' / w * w + i' % w := by rw [Nat.mul_comm]; exact (Nat.div_add_mod i' w).symm
      generalize hJ : i' / w = j at hj hi'
      generalize hQ : i' % w = q at hq hi'
      subst hi'
      by_cases hj2 : j < 2
      · have e := VG.Proof.Ffdh.generationValues_montgomery k dom
        simp only [Spec.Rsa.modulusWords, hw] at e
        have e' := congrArg (fun l => l[j * w + q]?) e
        have hjw : j * w + q < 2 * w := by
          have := Nat.mul_le_mul_right w (show j + 1 ≤ 2 by omega); rw [Nat.succ_mul] at this; omega
        simp only [List.getElem?_take, hjw, ↓reduceIte, List.getElem?_drop] at e'
        rw [e']
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by
            rw [VG.Proof.Rsa.FixedBaseComb.toWords_length]; exact hq), toWords_get? hq]
          have := row_word (j := 0) hq hp; simp only [Nat.zero_mul, Nat.zero_add] at this; rw [this]
        · rw [Nat.one_mul, List.getElem?_append_right (by
            rw [VG.Proof.Rsa.FixedBaseComb.toWords_length]; omega), VG.Proof.Rsa.FixedBaseComb.toWords_length,
            show w + q - w = q by omega, toWords_get? hq]
          have := row_word (j := 1) hq hr; simp only [Nat.one_mul] at this; rw [this]
      · obtain ⟨a, rfl⟩ : ∃ a, j = a + 2 := ⟨j - 2, by omega⟩
        have e := VG.Proof.Ffdh.generationValues_entry k dom a (by omega)
        simp only [Spec.Rsa.modulusWords, hw] at e
        have e' := congrArg (fun l => l[q]?) e
        simp only [List.getElem?_take, hq, ↓reduceIte, List.getElem?_drop] at e'
        rw [show 3 + ((a + 2) * w + q) = 3 + (2 + a) * w + q by rw [Nat.add_comm a 2]; omega, e',
          toWords_get? hq, show 3 + (2 + a) * w + q = 3 + ((a + 2) * w + q) by rw [Nat.add_comm 2 a]; omega,
          row_word (j := a + 2) hq (he a (by omega))]
  · rw [List.getElem?_eq_none (by simp [Spec.Rsa.wordsAt]; omega), List.getElem?_eq_none (by omega)]

end VG.Proof.Ffdh.PPC64LE.Cached
