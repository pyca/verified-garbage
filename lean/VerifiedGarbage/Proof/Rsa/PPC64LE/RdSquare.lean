module
-- separate module: builds in parallel with the other stages of `det_ok` (`RdCorrect.lean`)

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdProd
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: `b²` and `b² - 4 n`

`square_ok`: `b = q + 1` and `b²` (`product`); `minus4n_ok`: `4 n`,
`b² - 4 n` and the borrows of `b² - 4 n` and `b² - 4 n - 1`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet (wsub wsub_neg prodStep)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.RecoverDet (square minus4n sB0 sB1 sLt sExact sC1 sC2)

section
variable {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat}

/-- `square`: `b = q + 1` (narrow `aD`), and `b²` (wide `wA`). -/
theorem square_ok (h : DS s0 false A dbL V [sExact, sLt, sB1, sB0] s) (z : A true 15 = 0)
    (n1 : A false 23 = wsub (32 * ww (kK s0)) 0 1) :
    WP isa square s fun t => ∃ A' V', DS s0 true A' (pL 14) V' [sExact, sLt, sB1, sB0] t ∧
      A' false 25 = (A false 25 + 1) % 2 ^ (32 * ww (kK s0)) ∧
      A' true 17 = ((prodStep (32 * vw s0 true))^[32 * ww (kK s0)] ((A false 25 + 1) % 2 ^ (32 * ww (kK s0)),
        (A false 25 + 1) % 2 ^ (32 * ww (kK s0)), 0)).2.2 ∧
      A' true 15 = 0 ∧ A' true 9 = A true 9 ∧ A' true 19 = A true 19 ∧
      (∀ d ∈ [sExact, sLt, sB1, sB0], V' d = V d) := by
  have w1 := h.base.sz.w1
  have P1 : 1 < 2 ^ (32 * ww (kK s0)) := Nat.one_lt_two_pow (by omega)
  have l25 := h.lt (b' := false) (j := 25) (by decide)
  rw [vw_false] at l25
  unfold square
  simp only [seqs]
  refine WP.seq (WP.mono (h.sub3 (o := 25) (a := 25) (c := 23) (by decide) (by decide) (by decide)
    (live' := [(false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun s1 ⟨h1, _, _⟩ => ?_)
  have hb : wsub (32 * ww (kK s0)) (A false 25) (A false 23) = (A false 25 + 1) % 2 ^ (32 * ww (kK s0)) := by
    rw [n1, wsub_neg l25 P1]
  refine WP.seq (WP.mono h1.toWB fun s2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.copy (o := 14) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(false, 25), (true, 19), (true, 15), (true, 9)]) (by decide)) fun s3 ⟨h3, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.copy (o := 8) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(true, 14), (false, 25), (true, 19), (true, 15), (true, 9)]) (by decide)) fun s4 ⟨h4, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.copy (o := 17) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(true, 8), (true, 14), (false, 25), (true, 19), (true, 15), (true, 9)]) (by decide))
    fun s5 ⟨h5, _, _⟩ => ?_)
  refine WP.seq (WP.mono h5.toNB fun s6 ⟨h6, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.widen (k := 14) (a := 25) (by decide) (by decide) (by rd_simp [z]) (by decide)
    (by decide) (live' := [(true, 17), (true, 8), (false, 25), (true, 19), (true, 15), (true, 9)]) (by decide))
    fun s7 ⟨h7, _⟩ => ?_)
  refine WP.seq (WP.mono (h7.widen (k := 8) (a := 25) (by decide) (by decide) (by rd_simp [z]) (by decide)
    (by decide) (live' := [(true, 14), (true, 17), (false, 25), (true, 19), (true, 15), (true, 9)]) (by decide))
    fun s8 ⟨h8, _⟩ => ?_)
  refine WP.seq (WP.block_append (WP.mono h8.countN fun s9 ⟨h9, c9, _⟩ =>
    WP.mono h9.toWB fun s10 ⟨h10, k10⟩ => ?_))
  have c10 : s10.gpr .r27 = BitVec.ofNat 64 (32 * ww (kK s0)) := by rw [k10.gpr _ (by decide)]; exact c9
  show WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.product 8 14 17 11 20 15) s10 _
  refine WP.mono (product_ok (x := 14) (ls := [sExact, sLt, sB1, sB0]) (.inr rfl) (h10.drop (by decide) (by decide))
    (by rd_simp [z]) (by decide) c10) fun t ⟨A', V', ht, e, z', r, v⟩ => ⟨A', V', ht, ?_, ?_, z', ?_, ?_, v⟩
  · rw [r (false, 25) (by decide)]; rd_simp [hb]
  · have e' := congrArg (fun p => p.2.2) e
    simp only at e'
    rw [e']
    rd_simp [hb, z]
  · rw [r (true, 9) (by decide)]; rd_simp
  · rw [r (true, 19) (by decide)]; rd_simp

/-- `minus4n`: `X = b² - 4 n` modulo `2^(32 W)`, and whether `b² < 4 n` and `X < 1`. -/
theorem minus4n_ok (h : DS s0 true A (pL 14) V [sExact, sLt, sB1, sB0] s) :
    WP isa minus4n s fun t => ∃ A' V', DS s0 true A' [(true, 18), (true, 15), (false, 25)] V'
        [sC2, sC1, sExact, sLt, sB1, sB0] t ∧
      A' true 18 = wsub (32 * vw s0 true) (A true 17) (VG.Proof.Rsa.RecoverDet.fourN (32 * vw s0 true) (A true 19)) ∧
      A' true 15 = A true 15 ∧ A' false 25 = A false 25 ∧
      V' sC1 = b2n (decide (A true 17 < VG.Proof.Rsa.RecoverDet.fourN (32 * vw s0 true) (A true 19))) ∧
      V' sC2 = b2n (decide (wsub (32 * vw s0 true) (A true 17)
        (VG.Proof.Rsa.RecoverDet.fourN (32 * vw s0 true) (A true 19)) < A true 9)) ∧
      (∀ d ∈ [sExact, sLt, sB1, sB0], V' d = V d) := by
  unfold minus4n
  simp only [seqs]
  refine WP.seq (WP.mono (h.shl (j := 19) (by decide)
    (live' := [(true, 8), (true, 14), (true, 17), (true, 15), (true, 9), (false, 25)]) (by decide))
    fun s1 ⟨h1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.shl (j := 19) (by decide)
    (live' := [(true, 17), (true, 15), (true, 9), (false, 25)]) (by decide)) fun s2 ⟨h2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.sub3 (o := 18) (a := 17) (c := 19) (by decide) (by decide) (by decide)
    (live' := [(true, 17), (true, 19), (true, 15), (true, 9), (false, 25)]) (by decide)) fun s3 ⟨h3, b3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.stBorrowB (sl := sC1) (by decide) b3 (by split <;> decide)
    (ls' := [sExact, sLt, sB1, sB0]) (by decide)) fun s4 ⟨h4, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.sub3 (o := 20) (a := 18) (c := 9) (by decide) (by decide) (by decide)
    (live' := [(true, 18), (true, 19), (true, 15), (true, 9), (false, 25)]) (by decide)) fun s5 ⟨h5, b5, _⟩ => ?_)
  refine WP.mono (h5.stBorrowB (sl := sC2) (by decide) b5 (by split <;> decide)
    (ls' := [sC1, sExact, sLt, sB1, sB0]) (by decide)) fun t ⟨ht, _⟩ =>
      ⟨_, _, ht.drop (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rd_simp [VG.Proof.Rsa.RecoverDet.fourN]

end

end VG.Proof.Rsa.PPC64LE.RecDet
