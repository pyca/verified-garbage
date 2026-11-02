module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdProd
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the divisions

`divA_ok`: `m = ⌊a / n⌋` and `r = a mod n` (wide), and whether `m < n`;
`divB_ok`: `n - r` divided by `m + 1` (narrow), and whether it is exact.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet (wsub)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.RecoverDet (divA divB sB0 sB1 sLt sExact)

section
variable {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat}

/-- `divA`: `m` and `r` of `a` by `n`, and whether `m < n`. -/
theorem divA_ok (h : DS s0 true A (pL 12) V [sB1, sB0] s) (z : A true 15 = 0) (pos : 0 < A false 32) :
    WP isa divA s fun t => ∃ A' V',
      DS s0 true A' [(true, 17), (true, 18), (true, 19), (true, 15), (true, 9), (false, 32)] V'
        [sLt, sB1, sB0] t ∧
      A' true 17 = A true 17 / A false 32 ∧ A' true 18 = A true 17 % A false 32 ∧ A' true 19 = A false 32 ∧
      A' true 15 = 0 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧
      V' sLt = b2n (decide (A true 17 / A false 32 < A false 32)) ∧ V' sB0 = V sB0 ∧ V' sB1 = V sB1 := by
  unfold divA
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy (o := 19) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(true, 17), (true, 15), (true, 9), (false, 32)]) (by decide)) fun s1 ⟨h1, _, _⟩ => ?_)
  refine WP.seq (WP.mono h1.toNB fun s2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.widen (k := 19) (a := 32) (by decide) (by decide) (by rd_simp [z]) (by decide)
    (by decide) (live' := [(true, 17), (true, 15), (true, 9), (false, 32)]) (by decide)) fun s3 ⟨h3, _⟩ => ?_)
  refine WP.seq (WP.mono h3.toWB fun s4 ⟨h4, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.clrWB (j := 19) (by decide)
    (live' := [(true, 17), (true, 15), (true, 9), (false, 32)]) (by decide)) fun s5 ⟨h5, z5, _⟩ => ?_)
  refine WP.seq (WP.mono (h5.div (q := 17) (r := 18) (d := 19) (t := 21) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) z5
    (live' := [(true, 19), (true, 15), (true, 9), (false, 32)]) (by decide)) fun s6 ⟨Q, R, h6, qr, _⟩ => ?_)
  have nz : 0 < upd (upd (upd (upd A true 19 (A true 15)) false (2 * 19) (A false 32)) true 19 (A false 32)) true 19
      (upd (upd (upd A true 19 (A true 15)) false (2 * 19) (A false 32)) true 19 (A false 32) true 19) true 19 := by
    rd_simp; exact pos
  obtain ⟨eq, er⟩ := qr nz
  refine WP.seq (WP.mono (h6.sub3 (o := 20) (a := 17) (c := 19) (by decide) (by decide) (by decide)
    (live' := [(true, 17), (true, 18), (true, 19), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun s7 ⟨h7, b7, _⟩ => ?_)
  refine WP.mono (h7.stBorrowB (sl := sLt) (by decide) b7 (by split <;> decide) (ls' := [sB1, sB0]) (by decide))
    fun t ⟨ht, _⟩ => ⟨_, _, ht.drop (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rd_simp [eq, er, z]

/-- The arrays after the second division: `b - 1`, `-1`, zero, `n` (wide), zero (wide), one (wide)
and `n`. -/
abbrev dbL : List (Bool × Nat) := [(false, 25), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)]

/-- `divB`: `n - r` by `m + 1` (narrow), and whether the remainder is zero. -/
theorem divB_ok (h : DS s0 true A [(true, 17), (true, 18), (true, 19), (true, 15), (true, 9), (false, 32)] V
      [sLt, sB1, sB0] s) (z : A true 15 = 0) :
    WP isa divB s fun t => ∃ Q R A' V', DS s0 false A' dbL V' [sExact, sLt, sB1, sB0] t ∧
      (0 < (A true 17 % 2 ^ (32 * ww (kK s0)) + 1) % 2 ^ (32 * ww (kK s0)) →
        Q = wsub (32 * ww (kK s0)) (A false 32) (A true 18 % 2 ^ (32 * ww (kK s0))) /
          ((A true 17 % 2 ^ (32 * ww (kK s0)) + 1) % 2 ^ (32 * ww (kK s0))) ∧
        R = wsub (32 * ww (kK s0)) (A false 32) (A true 18 % 2 ^ (32 * ww (kK s0))) %
          ((A true 17 % 2 ^ (32 * ww (kK s0)) + 1) % 2 ^ (32 * ww (kK s0)))) ∧
      A' false 25 = Q ∧ A' false 23 = wsub (32 * ww (kK s0)) 0 1 ∧ A' false 30 = 0 ∧ A' true 19 = A true 19 ∧
      A' true 15 = 0 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧
      V' sExact = b2n (decide (R = 0)) ∧ V' sLt = V sLt ∧ V' sB0 = V sB0 ∧ V' sB1 = V sB1 := by
  have w1 := h.base.sz.w1
  have P1 : 1 < 2 ^ (32 * ww (kK s0)) := Nat.one_lt_two_pow (by omega)
  have l17 := h.lt (b' := true) (j := 17) (by decide)
  unfold divB
  simp only [seqs]
  refine WP.seq (WP.mono h.toNB fun s1 ⟨h1, _⟩ => ?_)
  have h1a := ((h1.addLow (k := 15) (by decide) (by decide) (by decide)).addLow (k := 17) (by decide) (by decide)
    (by decide)).addLow (k := 18) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (h1a.copy (o := 22) (a := 30) (by decide) (by decide) (by decide)
    (live' := [(false, 36), (false, 34), (false, 30), (true, 17), (true, 18), (true, 19), (true, 15), (true, 9),
      (false, 32)]) (by decide)) fun s2 ⟨h2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.setOneB (j := 22) (by decide)
    (live' := [(false, 36), (false, 34), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s3 ⟨h3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.sub3 (o := 23) (a := 30) (c := 22) (by decide) (by decide) (by decide)
    (live' := [(false, 36), (false, 34), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s4 ⟨h4, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.sub3 (o := 24) (a := 34) (c := 23) (by decide) (by decide) (by decide)
    (live' := [(false, 23), (false, 36), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s5 ⟨h5, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h5.sub3 (o := 25) (a := 32) (c := 36) (by decide) (by decide) (by decide)
    (live' := [(false, 24), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s6 ⟨h6, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.clrWB (j := 24) (by decide)
    (live' := [(false, 25), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s7 ⟨h7, z7, _⟩ => ?_)
  refine WP.seq (WP.mono (h7.div (q := 25) (r := 26) (d := 24) (t := 27) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) z7
    (live' := [(false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun s8 ⟨Q, R, h8, qr, _⟩ => ?_)
  refine WP.mono (h8.eqS (d := sExact) (a := 26) (c := 30) (by decide) (by decide) (by decide)
    (ls' := [sLt, sB1, sB0]) (by decide)) fun t ⟨ht, _⟩ =>
      ⟨Q, R, _, _, ht.drop (by decide) (by decide), fun pos => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := qr (by rd_simp [z]; rw [wsub_neg (Nat.mod_lt _ (Nat.two_pow_pos _)) P1]; exact pos)
    rd_simp_at this [z]
    rw [wsub_neg (Nat.mod_lt _ (Nat.two_pow_pos _)) P1] at this
    exact this
  all_goals rd_simp [z]

end

end VG.Proof.Rsa.PPC64LE.RecDet
