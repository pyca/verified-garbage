module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# The precomputed values of an RSA modulus on PPC64LE: the check

`check_ok`: `check` leaves 0 in `r0` iff the `k` bytes at `N` make a valid
modulus (`Spec.Rsa.modulusValid`), for `64 ≤ k ≤ 1024`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute

theorem read_byte64 (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = BitVec.ofNat 64 (m a).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (m.read a 1).isLt (by decide)),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (m a).isLt (by decide))]
  show (m.read (a + 1) 0 ++ m a).toNat = (m a).toNat
  rw [BitVec.toNat_append]
  simp [Mem.read]

theorem odd_xor (x : Nat) :
    BitVec.ofNat 64 x &&& 1#64 ^^^ 1#64 = 0 ↔ x % 2 = 1 := by
  have e : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1#64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [e]
  rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h <;> rw [h] <;> decide

theorem top_xor {x : Nat} (hx : x < 256) : BitVec.ofNat 64 x >>> 7 ^^^ (1 : BitVec 64) = 0 ↔ 128 ≤ x := by
  have e : BitVec.ofNat 64 x >>> 7 = BitVec.ofNat 64 (x / 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e]
  rcases (show x / 128 = 0 ∨ x / 128 = 1 by omega) with h | h
  · rw [h]; constructor <;> intro h' <;> first | (exact absurd h' (by decide)) | omega
  · rw [h]; constructor <;> intro <;> first | decide | omega

theorem check1_ok {s : State} {N : Addr} {k : Nat} {nb : List Byte}
    (h12 : s.gpr .r12 = off N 0) (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (hk : 64 ≤ k)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (off N i) = nb[i]'(by omega)) :
    WP isa (.block check1) s fun t =>
      ((t.gpr .r0 = 0 ↔ (nb[k - 1]'(by omega)).toNat % 2 = 1) ∧
        t.gpr .r15 = BitVec.ofNat 64 (nb[0]'(by omega)).toNat ∧ t.gpr .r18 = 1 ∧ t.mem = s.mem) ∧
        Keep [.r0, .r15, .r18] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold check1
  have r0 := hrd 0 (by omega)
  have rl := hrd (k - 1) (by omega)
  have b0 := hb 0 (by omega)
  have bl := hb (k - 1) (by omega)
  prun [h12, h6, Nat.zero_add, off_sub1 N (show 1 ≤ k by omega), r0, rl, read_byte64, b0, bl, exec_lbz' (show Reg.r15 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    exec_lbz' (show Reg.r12 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide)]
  exact ⟨odd_xor _, rfl⟩

theorem check2_ok {s : State} {k : Nat} {nb : List Byte}
    (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (i0 : s.gpr .r0 = 0 ↔ (nb[k - 1]'(by omega)).toNat % 2 = 1)
    (i15 : s.gpr .r15 = BitVec.ofNat 64 (nb[0]'(by omega)).toNat) (i18 : s.gpr .r18 = 1) :
    WP isa check2 s fun t =>
      (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) ∧ t.mem = s.mem ∧
        Keep [.r0, .r15, .r16, .r18] s t := by
  have hB0 := (nb[0]'(by omega)).isLt
  have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true ↔ (1 ≤ (nb[0]'(by omega)).toNat ∧
      (nb[k - 1]'(by omega)).toNat % 2 = 1 ∧ 128 ≤ (k - 64) * 256 + (nb[0]'(by omega)).toNat) := by
    rw [modulusValid_iff hlen hk hk']
    simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
    omega
  have hrest : ∀ t₂ : State, (t₂.gpr .r0 = 0 ↔ 1 ≤ (nb[0]'(by omega)).toNat ∧
      (nb[k - 1]'(by omega)).toNat % 2 = 1) → t₂.gpr .r15 = BitVec.ofNat 64 (nb[0]'(by omega)).toNat →
      t₂.gpr .r18 = 1 → t₂.mem = s.mem → Keep [.r0, .r15, .r18] s t₂ →
      WP isa (.seq (.block [.subi .r16 .r6 64])
        (.ite (.zero .d .r16) (.block [.lsr .d .r15 .r15 7, .logic .xor .r15 .r15 .r18,
          .logic .or .r0 .r0 .r15]) (.block []))) t₂ fun t =>
        (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) ∧ t.mem = s.mem ∧
          Keep [.r0, .r15, .r16, .r18] s t := by
    intro t₂ j0 j15 j18 jm k₂
    refine WP.seq (WP.mono (WP.keep [.r16] (Q := fun t => t.gpr .r16 = BitVec.ofNat 64 (k - 64) ∧
      t.mem = t₂.mem) (by prun [k₂.gpr .r6 (by decide), h6, Offset.ofNat_sub_ofNat hk]) (by decide))
      fun t₃ ⟨⟨l16, lm⟩, k₃⟩ => ?_)
    have k23 := k₂.trans k₃
    refine WP.ite _ (eval_zero_ofNat _ _ (by omega) l16) (fun hz => ?_) (fun hz => ?_)
    · refine WP.mono (WP.keep [.r0, .r15] (Q := fun t =>
        t.gpr .r0 = t₃.gpr .r0 ||| (BitVec.ofNat 64 (nb[0]'(by omega)).toNat >>> 7 ^^^ (1 : BitVec 64)) ∧
          t.mem = t₃.mem) (by prun [k₃.gpr .r15 (by decide), k₃.gpr .r18 (by decide), j15, j18])
        (by decide)) fun t ⟨⟨m0, mm⟩, k₄⟩ => ⟨?_, by rw [mm, lm, jm], (k23.trans k₄).mono⟩
      rw [m0, show ∀ a b : BitVec 64, (a ||| b = 0 ↔ a = 0 ∧ b = 0) from fun _ _ => BitVec.or_eq_zero_iff, k₃.gpr .r0 (by decide), j0, top_xor hB0, hv]
      have : k = 64 := by simp at hz; omega
      subst this
      constructor <;> intro h <;> omega
    · refine wp_nil ⟨?_, by rw [lm, jm], k23.mono⟩
      rw [k₃.gpr .r0 (by decide), j0, hv]
      have : k ≠ 64 := by simp at hz; omega
      constructor <;> intro h <;> omega
  unfold check2
  refine WP.seq (WP.ite _ (eval_zero_ofNat _ _ (by omega) i15) (fun hz => ?_) (fun hz => ?_))
  · refine WP.mono (WP.keep [.r0] (Q := fun t => t.gpr .r0 = 1 ∧ t.mem = s.mem) (by prun; rfl) (by decide))
      fun t₂ ⟨⟨m0, mm⟩, k₂⟩ => hrest t₂ ?_ (by rw [k₂.gpr .r15 (by decide), i15])
        (by rw [k₂.gpr .r18 (by decide), i18]) mm k₂.mono
    have : (nb[0]'(by omega)).toNat = 0 := by simpa using hz
    rw [m0, this]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h.1 (by omega)⟩
  · refine wp_nil (hrest s ?_ i15 i18 rfl (Keep.refl _ _))
    have : (nb[0]'(by omega)).toNat ≠ 0 := by simpa using hz
    rw [i0]; omega

theorem check_ok {s : State} {N : Addr} {k : Nat} {nb : List Byte}
    (h12 : s.gpr .r12 = off N 0) (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (off N i) = nb[i]'(by omega)) :
    WP isa check s fun t =>
      (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) ∧ t.mem = s.mem ∧
        Keep [.r0, .r15, .r16, .r18] s t := by
  unfold check
  refine WP.seq (WP.mono (check1_ok h12 h6 hk hlen hrd hb) fun t₁ ⟨⟨i0, i15, i18, im⟩, k₁⟩ => ?_)
  refine WP.mono (check2_ok ((k₁.gpr .r6 (by decide)).trans h6) hk hk' hlen i0 i15 i18)
    fun t ⟨a, b, c⟩ => ⟨a, b.trans im, (k₁.trans c).mono⟩

end VG.Proof.Bignum.PPC64LE
