module
-- separate module: builds in parallel with the other stages of `det_ok` (`RdCorrect.lean`)

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the GCD

`gcd_ok`: `gcd(u, x)` of the halvings' `u` (odd) and `x`, by the batched
inverse on the narrow arrays, 1 where `u = 1`, into the zeroed wide `wY`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.RecoverDet (gcd sB0 sB1 sU1)

section
variable [VG.Proof.Rsa.PPC64LE.InvLaw] {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat}

/-- The GCD of `u` (wide 14) and `x` (wide 13) into the wide `wY` (8). -/
theorem gcd_ok (h : DS s0 true A twL V [sB1, sB0] s) (uodd : A true 14 % 2 = 1)
    (ulo : A true 14 < 2 ^ (32 * ww (kK s0))) (xlo : A true 13 < 2 ^ (32 * ww (kK s0))) (z8 : A true 8 = 0)
    (o42 : A false 42 = 1) :
    WP isa gcd s fun t => ∃ A' V', DS s0 false A' [(true, 8), (true, 12), (true, 15), (true, 9), (false, 32)] V'
        [sB1, sB0] t ∧
      A' true 8 = Nat.gcd (A true 14) (A true 13) ∧ A' true 12 = A true 12 ∧ A' true 15 = A true 15 ∧
      A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧ V' sB0 = V sB0 ∧ V' sB1 = V sB1 := by
  unfold gcd
  simp only [seqs]
  refine WP.seq (WP.mono h.toNB fun s1 ⟨h1, _⟩ => ?_)
  have h1a := (h1.addLow (k := 13) (by decide) (by decide) (by decide)).addLow (k := 14) (by decide) (by decide)
    (by decide)
  refine WP.seq (WP.mono (h1a.copy (o := 0) (a := 26) (by decide) (by decide) (by decide)
    (live' := [(false, 28), (false, 26), (true, 14), (true, 13), (true, 12), (true, 15), (true, 8), (true, 9),
      (false, 32), (false, 42)]) (by decide)) fun s2 ⟨h2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.copy (o := 8) (a := 28) (by decide) (by decide) (by decide)
    (live' := [(false, 0), (false, 28), (false, 26), (true, 14), (true, 13), (true, 12), (true, 15), (true, 8),
      (true, 9), (false, 32), (false, 42)]) (by decide)) fun s3 ⟨h3, _, _⟩ => ?_)
  refine WP.seq (WP.mono h3.set11 fun s4 ⟨h4, r11, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.inv r11 (by decide) (by decide) (by rd_simp [Nat.mod_eq_of_lt ulo, uodd])
    (live' := [(false, 8), (false, 0), (false, 28), (false, 26), (true, 14), (true, 13), (true, 12), (true, 15),
      (true, 8), (true, 9), (false, 32), (false, 42)]) (by decide)) fun s5 ⟨G, h5, hG, _⟩ => ?_)
  refine WP.seq (WP.mono (h5.eqS (d := sU1) (a := 8) (c := 42) (by decide) (by decide) (by decide)
    (ls' := [sB1, sB0]) (by decide)) fun s6 ⟨h6, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.sel (o := 1) (a := 1) (c := 42) (sl := sU1) (by decide) (by decide) (by decide)
    (by decide) (by rd_simp)
    (live' := [(false, 8), (false, 0), (true, 12), (true, 15), (true, 8), (true, 9), (false, 32), (false, 42)])
    (by decide)) fun s7 ⟨h7, _⟩ => ?_)
  refine WP.mono (h7.widen (k := 8) (a := 1) (by decide) (by decide) (by rd_simp [z8]) (by decide) (by decide)
    (live' := [(true, 12), (true, 15), (true, 9), (false, 32)]) (by decide)) fun t ⟨ht, _⟩ =>
      ⟨_, _, ht.drop (by decide) (by decide), ?_, by rd_simp, by rd_simp, by rd_simp, by rd_simp, by rd_simp,
        by rd_simp⟩
  -- The GCD, or 1 for `u = 1`.
  by_cases u1 : A true 14 = 1
  · rd_simp [Nat.mod_eq_of_lt ulo, Nat.mod_eq_of_lt xlo, u1, o42]
  · have g := hG (by rd_simp [Nat.mod_eq_of_lt ulo]; omega)
    rd_simp_at g [Nat.mod_eq_of_lt ulo, Nat.mod_eq_of_lt xlo]
    rd_simp [Nat.mod_eq_of_lt ulo, Nat.mod_eq_of_lt xlo, u1, o42, g, Nat.gcd_comm]

end

end VG.Proof.Rsa.PPC64LE.RecDet
