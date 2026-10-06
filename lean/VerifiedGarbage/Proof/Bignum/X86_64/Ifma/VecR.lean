import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: the vector code from the regions

`vecR_ok` is `vec_ok` from what the regions
hold: each number as the `4 R` limbs `to52` writes, `k₀` as the low 52 bits
of the inverse, and the bases' values with `R_X = 2^(64 w)` for `w = W`.
The powers of two keep variable exponents.
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (limbN limbN_lt lval_limbN pow2_le cop2)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The limbs of `v` at offset `c` of region `p`. -/
theorem limb_of {m : Mem} {F : Addr} {c p v : Nat}
    (h : ∀ k < l.L, word m F (l.D * p + c + l.off k) = BitVec.ofNat 64 (limbN v k))
    {j : Nat} (hj : j < l.L) : limb l m F (l.D * p + c) j = limbN v j := by
  rw [limb, h j hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := limbN_lt v j; omega)]

theorem val52_of (hl : LayOk l) {m : Mem} {F : Addr} {c p v : Nat}
    (h : ∀ k < l.L, word m F (l.D * p + c + l.off k) = BitVec.ofNat 64 (limbN v k))
    (hv : v < 2 ^ (64 * l.W + 1)) : val52 l m F (l.D * p + c) = v := by
  rw [val52, lval_congr fun j hj => limb_of h hj, lval_limbN]
  have h2 := pow2_le (a := 64 * l.W + 1) (b := 52 * l.L) (by have := conv_bounds hl; omega)
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv h2)

theorem two_mul_lt {k a : Nat} (h : a < 2 ^ k) : 2 * a < 2 ^ (k + 1) + 1 := by
  rw [Nat.pow_succ]; omega

theorem good_of (hl : LayOk l) {m : Mem} {F : Addr} {M : Nat → Nat} {c p v : Nat}
    (h : ∀ k < l.L, word m F (l.D * p + c + l.off k) = BitVec.ofNat 64 (limbN v k))
    (hv : v < 2 * M p) (hM : M p < 2 ^ (64 * l.W)) : Good l m F M c p := by
  have := two_mul_lt hM
  exact ⟨fun j hj => by rw [limb_of h hj]; exact limbN_lt v j, by rw [val52_of hl h (by omega)]; exact hv⟩

/-- The limbs of `v` at offset `c` of region `p` (as `Limbs` says, for each prime). -/
abbrev LimbsAt (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (F : Addr) (c : Nat) (v : Nat → Nat) : Prop :=
  ∀ p < 2, ∀ k < l.L, word m F (l.D * p + c + l.off k) = BitVec.ofNat 64 (limbN (v p) k)

theorem k0_of {M : Nat} {mi : BitVec 64} (h : (M % 2 ^ 64 * mi.toNat + 1) % 2 ^ 64 = 0) :
    (limbN M 0 * (mi &&& mask52).toNat + 1) % 2 ^ 52 = 0 := AmmSym.k0_of h

/-- `vec` from the regions: for each prime `M p` (odd, `w = W` words), `k₀`
from its inverse `mi p`, `2^dbls R mod M`, `x R`, `R` (`R = 2^(64 w)`) and
the last multiplier `Fin p`. -/
theorem vecR_ok (hl : LayOk l) {s : State} {F : Addr} {M K1 Xc Y Fin x : Nat → Nat} {mi : Nat → BitVec 64}
    {Q : Prop} {w R : Nat}
    (hw : w = l.W) (hR : R = 2 ^ (64 * w)) (hB : s.gpr .rbx = F) (hs : Scr s F (2 * l.D + 8))
    (hM : LimbsAt l s.mem F oM M) (hK : LimbsAt l s.mem F l.oK1 K1) (hX : LimbsAt l s.mem F l.oX Xc)
    (hY : LimbsAt l s.mem F l.oY Y) (hF : LimbsAt l s.mem F l.oFin Fin)
    (hk0 : ∀ p < 2, ∀ t < 4, word s.mem F (l.D * p + l.oK0 + 8 * t) = mi p &&& mask52)
    (hinv : ∀ p < 2, (M p % 2 ^ 64 * (mi p).toNat + 1) % 2 ^ 64 = 0)
    (hMlt : ∀ p < 2, M p < 2 ^ (64 * w)) (hModd : ∀ p < 2, M p % 2 = 1)
    (hKlt : ∀ p < 2, K1 p < M p) (hXlt : ∀ p < 2, Xc p < M p) (hYlt : ∀ p < 2, Y p < M p)
    (hFlt : ∀ p < 2, Fin p < 2 * M p)
    (vx : Q → ∀ p < 2, Xc p % M p = x p * R % M p)
    (vy : Q → ∀ p < 2, Y p % M p = R % M p)
    (vk : Q → ∀ p < 2, K1 p % M p = 2 ^ l.dbls * R % M p) :
    WP isa (vec l) s fun s' =>
      (∀ p < 2, Good l s'.mem F M l.oY p ∧
        (Q → val52 l s'.mem F (l.D * p + l.oY) % M p = x p ^ ev l s.mem F p l.E * Fin p % M p)) ∧
      Outside F 0 (2 * l.D + 8) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr &&& 0xFFFF := by
  subst hR hw
  obtain ⟨cb1, cb2, cb3, cb4, cb5⟩ := conv_bounds hl
  have hv : ∀ {c} {v : Nat → Nat}, LimbsAt l s.mem F c v → ∀ p < 2, v p < 2 * M p →
      val52 l s.mem F (l.D * p + c) = v p :=
    fun h p hp hlt => val52_of hl (h p hp) (by have := two_mul_lt (hMlt p hp); omega)
  have ar : Ar l s.mem F M (fun p => (mi p &&& mask52).toNat) := by
    refine ⟨fun p hp j hj => ?_, fun p hp => hv hM p hp (by have := hModd p hp; omega), fun p hp t ht => ?_,
      fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
    · rw [limb_of (hM p hp) hj]; exact limbN_lt _ _
    · rw [hk0 p hp t ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [BitVec.toNat_and, show mask52.toNat = 2 ^ 52 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)
    · rw [limb_of (hM p hp) (by simp only [Lay.L]; have := hl.bounds; omega)]; exact k0_of (hinv p hp)
    · have h4 : 4 * M p ≤ 2 ^ (64 * l.W + 2) := by
        have := hMlt p hp
        rw [Nat.pow_succ, Nat.pow_succ]; omega
      exact Nat.le_trans h4 (pow2_le (by omega))
  have e2 : 2 ^ (416 * l.R - 64 * l.W) = 2 ^ l.dbls * 2 ^ (64 * l.W) := by
    rw [← Nat.pow_add]; congr 1; simp only [Lay.dbls]; omega
  refine WP.mono (vec_ok hl (Q := Q) (x := x) hB hs ar (fun p hp => cop2 (hModd p hp) _)
    (fun p hp => good_of hl (hX p hp) (by have := hXlt p hp; omega) (hMlt p hp))
    (fun p hp => good_of hl (hY p hp) (by have := hYlt p hp; omega) (hMlt p hp))
    (fun p hp => good_of hl (hK p hp) (by have := hKlt p hp; omega) (hMlt p hp))
    (fun p hp => good_of hl (hF p hp) (hFlt p hp) (hMlt p hp))
    (fun q p hp => by rw [hv hX p hp (by have := hXlt p hp; omega)]; exact vx q p hp)
    (fun q p hp => by rw [Nat.one_mul, ← vy q p hp, hv hY p hp (by have := hYlt p hp; omega)])
    (fun q p hp => by rw [e2, ← vk q p hp, hv hK p hp (by have := hKlt p hp; omega)]))
    fun s' ⟨hy, ho, hr, hrd, hwr, hmx⟩ => ⟨fun p hp => ⟨(hy p hp).1, fun q => by
      rw [(hy p hp).2 q, hv hF p hp (hFlt p hp)]⟩, ho, hr, hrd, hwr, hmx⟩

end VG.Proof.Bignum.X86_64.Ifma
