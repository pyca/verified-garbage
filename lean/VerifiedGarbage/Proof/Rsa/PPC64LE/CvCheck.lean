module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_crt_values` on PPC64LE: the check of the modulus

`check_ok`: as `vg_rsa_public_precompute`'s (`Proof/Bignum/PPC64LE/PreCheck.lean`),
`check` leaves 0 in `r0` iff the `k` bytes at `N` (in `r9`, `k` in `r10`)
make a valid modulus (`Spec.Rsa.modulusValid`), for `64 ≤ k ≤ 1024`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.CrtValues (check check1 check2)

theorem check1_ok {s : State} {N : Addr} {k : Nat} {nb : List Byte}
    (h9 : s.gpr .r9 = off N 0) (h10 : s.gpr .r10 = BitVec.ofNat 64 k) (hk : 64 ≤ k)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (off N i) = nb[i]'(by omega)) :
    WP isa (.block check1) s fun t =>
      ((t.gpr .r0 = 0 ↔ (nb[k - 1]'(by omega)).toNat % 2 = 1) ∧
        t.gpr .r11 = BitVec.ofNat 64 (nb[0]'(by omega)).toNat ∧ t.mem = s.mem) ∧
        Keep [.r0, .r11, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold check1
  have r0 := hrd 0 (by omega)
  have rl := hrd (k - 1) (by omega)
  have b0 := hb 0 (by omega)
  have bl := hb (k - 1) (by omega)
  prun [h9, h10, Nat.zero_add, off_sub1 N (show 1 ≤ k by omega), r0, rl, read_byte64, b0, bl,
    exec_lbz' (show Reg.r11 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    exec_lbz' (show Reg.r9 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide)]
  exact odd_xor _

theorem check2_ok {s : State} {k : Nat} {nb : List Byte}
    (h10 : s.gpr .r10 = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (i0 : s.gpr .r0 = 0 ↔ (nb[k - 1]'(by omega)).toNat % 2 = 1)
    (i11 : s.gpr .r11 = BitVec.ofNat 64 (nb[0]'(by omega)).toNat) :
    WP isa check2 s fun t =>
      (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) ∧ t.mem = s.mem ∧
        Keep [.r0, .r11, .r12] s t := by
  have hB0 := (nb[0]'(by omega)).isLt
  have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true ↔ (1 ≤ (nb[0]'(by omega)).toNat ∧
      (nb[k - 1]'(by omega)).toNat % 2 = 1 ∧ 128 ≤ (k - 64) * 256 + (nb[0]'(by omega)).toNat) := by
    rw [modulusValid_iff hlen hk hk']
    simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
    omega
  have hrest : ∀ t₂ : State, (t₂.gpr .r0 = 0 ↔ 1 ≤ (nb[0]'(by omega)).toNat ∧
      (nb[k - 1]'(by omega)).toNat % 2 = 1) → t₂.gpr .r11 = BitVec.ofNat 64 (nb[0]'(by omega)).toNat →
      t₂.mem = s.mem → Keep [.r0, .r11, .r12] s t₂ →
      WP isa (.seq (.block [.subi .r12 .r10 64])
        (.ite (.zero .d .r12) (.block [.lsr .d .r11 .r11 7, .li .r12 1, .logic .xor .r11 .r11 .r12,
          .logic .or .r0 .r0 .r11]) (.block []))) t₂ fun t =>
        (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) ∧ t.mem = s.mem ∧
          Keep [.r0, .r11, .r12] s t := by
    intro t₂ j0 j11 jm k₂
    refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (k - 64) ∧
      t.mem = t₂.mem) (by prun [k₂.gpr .r10 (by decide), h10, Offset.ofNat_sub_ofNat hk]) (by decide))
      fun t₃ ⟨⟨l12, lm⟩, k₃⟩ => ?_)
    have k23 := k₂.trans k₃
    refine WP.ite _ (eval_zero_ofNat _ _ (by omega) l12) (fun hz => ?_) (fun hz => ?_)
    · refine WP.mono (WP.keep [.r0, .r11, .r12] (Q := fun t =>
        t.gpr .r0 = t₃.gpr .r0 ||| (BitVec.ofNat 64 (nb[0]'(by omega)).toNat >>> 7 ^^^ (1 : BitVec 64)) ∧
          t.mem = t₃.mem) (by prun [k₃.gpr .r11 (by decide), j11]; rfl)
        (by decide)) fun t ⟨⟨m0, mm⟩, k₄⟩ => ⟨?_, by rw [mm, lm, jm], (k23.trans k₄).mono⟩
      rw [m0, show ∀ a b : BitVec 64, (a ||| b = 0 ↔ a = 0 ∧ b = 0) from fun _ _ => BitVec.or_eq_zero_iff,
        k₃.gpr .r0 (by decide), j0, top_xor hB0, hv]
      have : k = 64 := by simp at hz; omega
      subst this
      constructor <;> intro h <;> omega
    · refine wp_nil ⟨?_, by rw [lm, jm], k23.mono⟩
      rw [k₃.gpr .r0 (by decide), j0, hv]
      have : k ≠ 64 := by simp at hz; omega
      constructor <;> intro h <;> omega
  unfold check2
  refine WP.seq (WP.ite _ (eval_zero_ofNat _ _ (by omega) i11) (fun hz => ?_) (fun hz => ?_))
  · refine WP.mono (WP.keep [.r0] (Q := fun t => t.gpr .r0 = 1 ∧ t.mem = s.mem) (by prun; rfl) (by decide))
      fun t₂ ⟨⟨m0, mm⟩, k₂⟩ => hrest t₂ ?_ (by rw [k₂.gpr .r11 (by decide), i11]) mm k₂.mono
    have : (nb[0]'(by omega)).toNat = 0 := by simpa using hz
    rw [m0, this]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h.1 (by omega)⟩
  · refine wp_nil (hrest s ?_ i11 rfl (Keep.refl _ _))
    have : (nb[0]'(by omega)).toNat ≠ 0 := by simpa using hz
    rw [i0]; omega

theorem check_ok {s : State} {N : Addr} {k : Nat} {nb : List Byte}
    (h9 : s.gpr .r9 = off N 0) (h10 : s.gpr .r10 = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (off N i) = nb[i]'(by omega)) :
    WP isa check s fun t =>
      (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) ∧ t.mem = s.mem ∧
        Keep [.r0, .r11, .r12] s t := by
  unfold check
  refine WP.seq (WP.mono (check1_ok h9 h10 hk hlen hrd hb) fun t₁ ⟨⟨i0, i11, im⟩, k₁⟩ => ?_)
  refine WP.mono (check2_ok ((k₁.gpr .r10 (by decide)).trans h10) hk hk' hlen i0 i11)
    fun t ⟨a, b, c⟩ => ⟨a, b.trans im, (k₁.trans c).mono⟩

end VG.Proof.Rsa.PPC64LE.CrtValues
