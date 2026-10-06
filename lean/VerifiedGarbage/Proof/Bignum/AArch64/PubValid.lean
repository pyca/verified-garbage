import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup

/-!
# RSA on AArch64: the check of the modulus

`invalid` leaves 1 in `x9` iff the `k` bytes of `m` make a valid modulus
(`Spec.Rsa.modulusValid`), and 0 if not, for `64 ≤ k ≤ 1024`
(`invalid_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep read_one)

theorem byte_toNat (b : Byte) : (BitVec.setWidth 64 (BitVec.setWidth 32 b)).toNat = b.toNat := by
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

/-- `subs` of a small constant `c`, then `csel` of 1 and 0: whether `c ≤ x`. -/
theorem ge_sel {x c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 16) (v : BitVec 64) (hv : v.toNat = x) :
    (if decide (2 ^ 64 ≤ v.toNat + (~~~BitVec.setWidth 64 (BitVec.ofNat 16 c)).toNat + true.toNat) = true then
        BitVec.setWidth 64 (1#16) else BitVec.setWidth 64 (0#16)) = BitVec.ofNat 64 (decide (c ≤ x)).toNat := by
  have e : (~~~BitVec.setWidth 64 (BitVec.ofNat 16 c)).toNat = 2 ^ 64 - 1 - c := by
    rw [BitVec.toNat_not, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hv, e, show true.toNat = 1 from rfl]
  by_cases h : c ≤ x
  · have h' : 2 ^ 64 ≤ x + (2 ^ 64 - 1 - c) + 1 := by omega
    simp only [h', h, decide_true, ite_true]; rfl
  · have h' : ¬ 2 ^ 64 ≤ x + (2 ^ 64 - 1 - c) + 1 := by omega
    simp only [h', h, decide_false, Bool.false_eq_true, ite_false]; rfl

theorem odd_sel (b : Byte) : BitVec.setWidth 64 (BitVec.setWidth 32 b) &&& BitVec.setWidth 64 (1#16) =
    BitVec.ofNat 64 (b.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, byte_toNat, show (BitVec.setWidth 64 (1#16)).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

theorem top_val {k : Nat} (b : Byte) (hk : 64 ≤ k) (hk' : k ≤ 1024) :
    ((BitVec.ofNat 64 k - 64#64) <<< 8 + BitVec.setWidth 64 (BitVec.setWidth 32 b)).toNat = (k - 64) * 256 + b.toNat := by
  have hb := b.isLt
  have e : BitVec.ofNat 64 k - 64#64 = BitVec.ofNat 64 (k - 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, byte_toNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]
  omega

theorem ge_not_lt (c x : Nat) : decide (c ≤ x) = !decide (x < c) := by
  by_cases h : c ≤ x
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem and3 (a c : Bool) (n : Nat) (hn : n < 2) :
    BitVec.ofNat 64 a.toNat &&& BitVec.ofNat 64 n &&& BitVec.ofNat 64 c.toNat =
      BitVec.ofNat 64 (a && decide (n = 1) && c).toNat := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> cases a <;> cases c <;> decide

theorem invalid_ok {s : State} {np : Addr} {k : Nat} {nb : List Byte}
    (h2 : s.gpr .x2 = np) (h3 : s.gpr .x3 = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (np + BitVec.ofNat 64 i) 1)
    (hb : ∀ i (h : i < k), s.mem (np + BitVec.ofNat 64 i) = nb[i]'(by omega)) :
    WP isa (.block invalid) s fun t =>
      t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k).toNat ∧ t.mem = s.mem ∧
      Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] s t := by
  have hr0 : InRegions (s.rd ++ s.wr) np 1 := by have := hrd 0 (by omega); rwa [off_zero] at this
  have hb0 : s.mem np = nb[0]'(by omega) := by have := hb 0 (by omega); rwa [off_zero] at this
  have hlast : np + (BitVec.ofNat 64 k - BitVec.ofNat 64 1) = np + BitVec.ofNat 64 (k - 1) := by
    rw [ofNat_sub_one' (by omega) (by omega)]
  have hn0 := (nb[0]'(by omega)).isLt
  unfold invalid
  rw [show ([.ldrb .x5 .x2 0, .subImm .x .x6 .x3 1, .add .x .x6 .x2 .x6, .ldrb .x6 .x6 0, movi .x7 0, movi .x8 1,
    .subs .x .x10 .x5 .x8, .csel .x .x10 .x8 .x7, .logic .and .x .x6 .x6 .x8,
    .subImm .x .x11 .x3 64, .lsl .x .x11 .x11 8, .add .x .x11 .x11 .x5, movi .x12 128,
    .subs .x .x12 .x11 .x12, .csel .x .x11 .x8 .x7, .logic .and .x .x9 .x10 .x6,
    .logic .and .x .x9 .x9 .x11] : List Instr) =
    ([.ldrb .x5 .x2 0, .subImm .x .x6 .x3 1, .add .x .x6 .x2 .x6, .ldrb .x6 .x6 0, movi .x7 0, movi .x8 1,
    .subs .x .x10 .x5 .x8, .csel .x .x10 .x8 .x7, .logic .and .x .x6 .x6 .x8,
    .subImm .x .x11 .x3 64, .lsl .x .x11 .x11 8, .add .x .x11 .x11 .x5, movi .x12 128,
    .subs .x .x12 .x11 .x12, .csel .x .x11 .x8 .x7] : List Instr) ++
    ([.logic .and .x .x9 .x10 .x6, .logic .and .x .x9 .x9 .x11] : List Instr) from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x10, .x11, .x12] (Q := fun t =>
      t.gpr .x10 = BitVec.ofNat 64 (decide (1 ≤ (nb[0]'(by omega)).toNat)).toNat ∧
      t.gpr .x6 = BitVec.ofNat 64 ((nb[k - 1]'(by omega)).toNat % 2) ∧
      t.gpr .x11 = BitVec.ofNat 64 (decide (128 ≤ (k - 64) * 256 + (nb[0]'(by omega)).toNat)).toNat ∧
      t.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h10, h6, h11, hm₁⟩, k₁⟩ => ?_
  · brun [h2, h3, hr0, read_one, hb0, hlast, hrd (k - 1) (by omega), hb (k - 1) (by omega)]
    refine ⟨ge_sel (by decide) (by decide) _ (byte_toNat _), odd_sel _,
      ge_sel (by decide) (by decide) _ (top_val _ hk hk')⟩
  refine WP.mono (WP.keep [.x9] (Q := fun t => t.gpr .x9 = t₁.gpr .x10 &&& t₁.gpr .x6 &&& t₁.gpr .x11 ∧
      t.mem = t₁.mem) (by brun) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h9, hm⟩, k₂⟩ => ⟨?_, hm.trans hm₁, (k₁.trans k₂).mono (by decide)⟩
  rw [h9, h10, h6, h11, and3 _ _ _ (Nat.mod_lt _ (by decide)), modulusValid_iff hlen hk hk']
  congr 2
  have hm := Nat.mod_lt (nb[k - 1]'(by omega)).toNat (show 0 < 2 by decide)
  rw [Bool.not_or, Bool.not_or, ge_not_lt, ge_not_lt, show decide ((nb[k - 1]'(by omega)).toNat % 2 = 1) =
    !decide ((nb[k - 1]'(by omega)).toNat % 2 < 1) by
      rcases (show (nb[k - 1]'(by omega)).toNat % 2 = 0 ∨ (nb[k - 1]'(by omega)).toNat % 2 = 1 by omega)
        with h | h <;> rw [h] <;> rfl]

end VG.Proof.Bignum.AArch64
