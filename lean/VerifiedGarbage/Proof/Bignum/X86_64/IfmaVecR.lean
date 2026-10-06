import VerifiedGarbage.Proof.Bignum.X86_64.IfmaConv

/-!
# RSA with AVX512_IFMA on x86-64: the vector code from the regions

`vecR_ok` is `vec_ok` from what the regions hold: each number as the twenty
limbs `to52` writes, `k₀` as the low 52 bits of the inverse, and the bases'
values with `R = 2^(64 w)` for `w = 16`.

This module imports no more of Mathlib than `vec_ok`'s, so that its powers
of two are elaborated as in `vec_ok` (core's `instPowNat`); its callers,
which import Mathlib's monoids, pass them with the exponent `64 w` a
variable, which unfolds to the same term without evaluating it.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oX oY oFin mask52)

/-- The limbs of `v` at offset `c` of region `p`. -/
theorem limb_of {m : Mem} {F : Addr} {c p v : Nat}
    (h : ∀ k < 20, word m F (D * p + c + VG.Impl.Rsa.X86_64.CrtIfma.off k) = BitVec.ofNat 64 (limbN v k))
    {j : Nat} (hj : j < 20) : limb m F (D * p + c) j = limbN v j := by
  rw [limb, h j hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := limbN_lt v j; omega)]

theorem val52_of {m : Mem} {F : Addr} {c p v : Nat}
    (h : ∀ k < 20, word m F (D * p + c + VG.Impl.Rsa.X86_64.CrtIfma.off k) = BitVec.ofNat 64 (limbN v k))
    (hv : v < 2 ^ (64 * 16 + 1)) : val52 m F (D * p + c) = v := by
  rw [val52, lval_congr fun j hj => limb_of h hj, lval_limbN]
  have h2 := pow2_le (a := 64 * 16 + 1) (b := 52 * 20) (by decide)
  generalize 2 ^ (64 * 16 + 1) = a at hv h2
  generalize 2 ^ (52 * 20) = b at h2 ⊢
  exact Nat.mod_eq_of_lt (by omega)

theorem good_of {m : Mem} {F : Addr} {M : Nat → Nat} {c p v : Nat}
    (h : ∀ k < 20, word m F (D * p + c + VG.Impl.Rsa.X86_64.CrtIfma.off k) = BitVec.ofNat 64 (limbN v k))
    (hv : v < 2 * M p) (hM : M p < 2 ^ (64 * 16)) : Good m F M c p := by
  have h3 : ∀ k a, a < 2 ^ k → 2 * a ≤ 2 ^ (k + 1) := fun k a h => by rw [Nat.pow_succ]; omega
  have := h3 _ _ hM
  exact ⟨fun j hj => by rw [limb_of h hj]; exact limbN_lt v j, by rw [val52_of h (by omega)]; exact hv⟩

/-- `k₀ = minv mod 2⁵²` from `minv`, the inverse of `-M` modulo `2⁶⁴`. -/
theorem k0_of {M : Nat} {mi : BitVec 64} (h : (M % 2 ^ 64 * mi.toNat + 1) % 2 ^ 64 = 0) :
    (limbN M 0 * (mi &&& mask52).toNat + 1) % 2 ^ 52 = 0 := by
  have hm : (mi &&& mask52).toNat = mi.toNat % 2 ^ 52 := by
    rw [BitVec.toNat_and, show mask52.toNat = 2 ^ 52 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [hm, limbN, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  have hd : 2 ^ 52 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by decide)
  have h1 : ∀ a b : Nat, (a % 2 ^ 52 * (b % 2 ^ 52) + 1) % 2 ^ 52 = (a * b + 1) % 2 ^ 52 := fun a b => by
    rw [Nat.add_mod (a % 2 ^ 52 * (b % 2 ^ 52)), ← Nat.mul_mod, ← Nat.add_mod]
  have h3 : (M % 2 ^ 64 * mi.toNat + 1) % 2 ^ 52 = 0 := by rw [← Nat.mod_mod_of_dvd _ hd, h, Nat.zero_mod]
  rw [h1, ← h3, ← h1 (M % 2 ^ 64), Nat.mod_mod_of_dvd _ hd]
  exact (h1 M _).symm

/-- `2^k` and an odd number are coprime (with core's powers, as `vec_ok` states it). -/
theorem cop2 {m : Nat} (hm : m % 2 = 1) (k : Nat) : Nat.Coprime (2 ^ k) m :=
  Nat.Coprime.pow_left k (by show Nat.gcd 2 m = 1; rw [Nat.gcd_rec, hm]; rfl)

/-- `cop2` for `R = 2¹⁰⁴⁰`; an instance of `cop2` at the closed exponent would be evaluated when checked. -/
theorem cop1040 {m : Nat} (hm : m % 2 = 1) : Nat.Coprime (2 ^ (52 * 20)) m := by
  generalize 52 * 20 = k; exact cop2 hm k

/-- The limbs of `v` at offset `c` of region `p` (as `Limbs` says, for each prime). -/
abbrev LimbsAt (m : Mem) (F : Addr) (c : Nat) (v : Nat → Nat) : Prop :=
  ∀ p < 2, ∀ k < 20, word m F (D * p + c + VG.Impl.Rsa.X86_64.CrtIfma.off k) = BitVec.ofNat 64 (limbN (v p) k)

/-- `vec` from the regions: for each prime `M p` (odd, `w = 16` words), `k₀`
from its inverse `mi p`, `2¹⁰⁵⁶ mod M`, `x R`, `R` (`R = 2^(64 w)`) and the
last multiplier `Fin p`. -/
theorem vecR_ok {s : State} {F : Addr} {M K1 Xc Y Fin x : Nat → Nat} {mi : Nat → BitVec 64} {Q : Prop} {w R : Nat}
    (hw : w = 16) (hR : R = 2 ^ (64 * w)) (hB : s.gpr .rbx = F) (hs : Scr s F (2 * D + 8))
    (hM : LimbsAt s.mem F oM M) (hK : LimbsAt s.mem F oK1 K1) (hX : LimbsAt s.mem F oX Xc)
    (hY : LimbsAt s.mem F oY Y) (hF : LimbsAt s.mem F oFin Fin)
    (hk0 : ∀ p < 2, ∀ t < 4, word s.mem F (D * p + oK0 + 8 * t) = mi p &&& mask52)
    (hinv : ∀ p < 2, (M p % 2 ^ 64 * (mi p).toNat + 1) % 2 ^ 64 = 0)
    (hMlt : ∀ p < 2, M p < 2 ^ (64 * w)) (hModd : ∀ p < 2, M p % 2 = 1)
    (hKlt : ∀ p < 2, K1 p < M p) (hXlt : ∀ p < 2, Xc p < M p) (hYlt : ∀ p < 2, Y p < M p)
    (hFlt : ∀ p < 2, Fin p < 2 * M p)
    (vx : Q → ∀ p < 2, Xc p % M p = x p * R % M p)
    (vy : Q → ∀ p < 2, Y p % M p = R % M p)
    (vk : Q → ∀ p < 2, K1 p % M p = 2 ^ 32 * R % M p) :
    WP isa VG.Impl.Rsa.X86_64.CrtIfma.vec s fun s' =>
      (∀ p < 2, Good s'.mem F M oY p ∧ (Q → val52 s'.mem F (D * p + oY) % M p = x p ^ ev s.mem F p 128 * Fin p % M p)) ∧
      Outside F 0 (2 * D + 8) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr &&& 0xFFFF := by
  -- Closed powers are never compared (`isDefEq` would evaluate them): rewrite the exponents.
  subst hR
  have e1 : 64 * w = 1024 := by omega
  rw [e1] at vx vy vk
  rw [hw] at hMlt
  have h3 : ∀ k a, a < 2 ^ k → 2 * a ≤ 2 ^ (k + 1) := fun k a h => by rw [Nat.pow_succ]; omega
  have hv : ∀ {c} {v : Nat → Nat}, LimbsAt s.mem F c v → ∀ p < 2, v p < 2 * M p → val52 s.mem F (D * p + c) = v p :=
    fun h p hp hlt => val52_of (h p hp) (by have := h3 _ _ (hMlt p hp); omega)
  have hb := fun p hp => h3 _ _ (hMlt p hp)
  have hb2 := pow2_le (a := 64 * 16 + 1) (b := 52 * 20) (by decide)
  have hb3 := pow2_le (a := 64 * 16 + 2) (b := 52 * 20) (by decide)
  have h4 : ∀ k a, a < 2 ^ k → 4 * a ≤ 2 ^ (k + 2) := fun k a h => by rw [Nat.pow_succ, Nat.pow_succ]; omega
  have ar : Ar s.mem F M (fun p => (mi p &&& mask52).toNat) := by
    refine ⟨fun p hp j hj => ?_, fun p hp => hv hM p hp (by have := hModd p hp; omega), fun p hp t ht => ?_,
      fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
    · rw [limb_of (hM p hp) hj]; exact limbN_lt _ _
    · rw [hk0 p hp t ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [BitVec.toNat_and, show mask52.toNat = 2 ^ 52 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)
    · rw [limb_of (hM p hp) (by decide)]; exact k0_of (hinv p hp)
    · have := h4 _ _ (hMlt p hp)
      generalize 2 ^ (64 * 16 + 2) = a at this hb3
      generalize 2 ^ (52 * 20) = b at hb3 ⊢
      omega
  refine WP.mono (vec_ok (Q := Q) (x := x) hB hs ar (fun p hp => cop1040 (hModd p hp))
    (fun p hp => good_of (hX p hp) (by have := hXlt p hp; omega) (hMlt p hp))
    (fun p hp => good_of (hY p hp) (by have := hYlt p hp; omega) (hMlt p hp))
    (fun p hp => good_of (hK p hp) (by have := hKlt p hp; omega) (hMlt p hp))
    (fun p hp => good_of (hF p hp) (hFlt p hp) (hMlt p hp))
    (fun q p hp => by rw [hv hX p hp (by have := hXlt p hp; omega)]; exact vx q p hp)
    (fun q p hp => by
      have h := vy q p hp
      generalize 2 ^ 1024 = R at h ⊢
      rw [Nat.one_mul, ← h, hv hY p hp (by have := hYlt p hp; omega)])
    (fun q p hp => by
      have h := vk q p hp
      have e := Nat.pow_add 2 32 1024
      rw [show 32 + 1024 = 1056 from rfl] at e
      generalize 2 ^ 1024 = R₂ at e h
      generalize 2 ^ 1056 = R₁ at e ⊢
      rw [e, ← h, hv hK p hp (by have := hKlt p hp; omega)]))
    fun s' ⟨hy, ho, hr, hrd, hwr, hmx⟩ => ⟨fun p hp => ⟨(hy p hp).1, fun q => by
      rw [(hy p hp).2 q, hv hF p hp (hFlt p hp)]⟩, ho, hr, hrd, hwr, hmx⟩

end VG.Proof.Bignum.X86_64.AmmSym
