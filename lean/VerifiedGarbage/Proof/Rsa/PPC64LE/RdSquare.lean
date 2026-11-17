module

-- separate module: builds in parallel with the other stages of `det_ok` (`RdCorrect.lean`)
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdMulW

/-! ### `Rsa.PPC64LE.RdProd`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the products

`DS.mulW`: the wide product (array 17) of the low `w` digits of the
multiplier (array 8) and the multiplicand, by rows of words (`Recover.mulW`), as the
`32 w` steps of `RecoverDet.prodStep` state it (`RecoverDet.prod_iter`);
`aProduct_ok`: `a = gcd(u, x) 2^k x`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet (wsub wsub_neg prodStep)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.RecoverDet (aProduct sB0 sB1)

section
variable {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat} {ls : List Nat} {live : List (Bool × Nat)}

/-- `r4 := w / 2`, the multiplier's words for `mulW`. -/
theorem DS.len4 (h : DS s0 false A live V ls s) :
    WP isa (.block [.lsr .d .r4 .r29 1]) s fun u => DS s0 false A live V ls u ∧
      u.gpr .r4 = BitVec.ofNat 64 (ww (kK s0) / 2) ∧ Keep [.r4] s u := by
  have := h.base.sz.w2
  have r29 : s.gpr .r29 = BitVec.ofNat 64 (ww (kK s0)) := h.ws.r29
  exact h.reg [.r4] (by prun [r29, Recover.shr_ofNat (show ww (kK s0) < 2 ^ 64 by omega_using [this])]) (by decide)

/-- The low `w` digits of a wide number. -/
theorem val32_low_w {m : Mem} {B : Addr} {d w : Nat} :
    val32 m B d w = val32 m B d (w + (w + 2)) % 2 ^ (32 * w) := by
  rw [val32_append, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

/-- `mulW o x y` on the wide view, `r4 = w / 2`: `[o] := ([x] mod 2^(32 w)) [y]` modulo `2^(32 W)`. -/
theorem DS.mulW (h : DS s0 true A live V ls s) {o x y : Nat} (ho : o < vN true) (hx : (true, x) ∈ live)
    (hy : (true, y) ∈ live) (hox : o ≠ x) (hoy : o ≠ y)
    (c4 : s.gpr .r4 = BitVec.ofNat 64 (ww (kK s0) / 2))
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (true, o) e) :
    WP isa (VG.Impl.Rsa.PPC64LE.Recover.mulW o x y) s fun t =>
      DS s0 true (upd A true o (A true x % 2 ^ (32 * ww (kK s0)) * A true y % 2 ^ (32 * vw s0 true)))
        ((true, o) :: live') V ls t := by
  have w1 := h.base.sz.w1
  have eW : vw s0 true = 2 * ww (kK s0) + 2 := by rw [vw_wide, vw_false]
  have ev : ww (kK s0) % 2 = 0 := by simp only [ww]; omega_using []
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Recover.mulW_ok (R := ww (kK s0) / 2) h.ws (vN_le true) ho (h.ix hx)
    (h.ix hy) hox hoy (by rw [eW]; omega_using []) c4 (by omega_using [w1]) (by rw [eW]; omega_using []))
    fun t ⟨ws, k, v, kr⟩ => h.wr ws ho k ?_ hl kr
  have e2 : 2 * (vw s0 true / 2) = vw s0 true := by rw [eW]; omega_using []
  have e64 : 64 * (vw s0 true / 2) = 32 * vw s0 true := by rw [eW]; omega_using []
  have ex : 2 * (ww (kK s0) / 2) = ww (kK s0) := by omega_using [ev]
  have conv : ∀ m d, val32 m (rvB s0) d (vw s0 true) = wordsVal m (rvB s0) d (vw s0 true / 2) := fun m d => by
    rw [wordsVal_eq_val32, e2]
  show val32 t.mem _ _ (vw s0 true) = _
  have vy : val32 s.mem (rvB s0) (KeyWorkspace.arr (vw s0 true) y) (vw s0 true) = A true y := h.val hy
  have vx : val32 s.mem (rvB s0) (KeyWorkspace.arr (vw s0 true) x) (vw s0 true) = A true x := h.val hx
  rw [conv, v, e64, ← conv, wordsVal_eq_val32, ex, vy, val32_low_w,
    show ww (kK s0) + (ww (kK s0) + 2) = vw s0 true by rw [eW]; omega_using [], vx]

/-- `a = gcd(u, x) 2^k x` modulo `2^(32 W)`, from the GCD in the wide `wY` and `2^k x` in `wX3`. -/
theorem aProduct_ok (h : DS s0 false A [(true, 8), (true, 12), (true, 15), (true, 9), (false, 32)] V [sB1, sB0] s)
    (z : A true 15 = 0) :
    WP isa aProduct s fun t => ∃ A' V', DS s0 true A' (pL 12) V' [sB1, sB0] t ∧
      A' true 17 = ((prodStep (32 * vw s0 true))^[32 * ww (kK s0)] (A true 8, A true 12, 0)).2.2 ∧
      A' true 15 = 0 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧ V' sB0 = V sB0 ∧ V' sB1 = V sB1 := by
  unfold aProduct
  simp only [seqs]
  refine WP.seq (WP.block_append (WP.mono h.len4 fun s1 ⟨h1, c1, _⟩ =>
    WP.mono h1.toWB fun s2 ⟨h2, k2⟩ => ?_))
  have c2 : s2.gpr .r4 = BitVec.ofNat 64 (ww (kK s0) / 2) := by rw [k2.gpr _ (by decide)]; exact c1
  have l12 := h2.lt (b' := true) (j := 12) (by decide)
  refine WP.mono (h2.mulW (o := 17) (x := 8) (y := 12) (by decide) (by decide) (by decide) (by decide)
    (by decide) c2 (live' := [(true, 8), (true, 12), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun t ht => ⟨_, V, ht.drop (by decide) (by decide), ?_, by rd_simp [z], by rd_simp, by rd_simp, rfl, rfl⟩
  rw [VG.Proof.Rsa.RecoverDet.prod_iter _ _ _ l12]
  rd_simp

end

end VG.Proof.Rsa.PPC64LE.RecDet

end

end

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
  have P1 : 1 < 2 ^ (32 * ww (kK s0)) := Nat.one_lt_two_pow (by omega_using [w1])
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
  refine WP.seq (WP.mono h4.toNB fun s6 ⟨h6, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.widen (k := 14) (a := 25) (by decide) (by decide) (by rd_simp [z]) (by decide)
    (by decide) (live' := [(true, 8), (false, 25), (true, 19), (true, 15), (true, 9)]) (by decide))
    fun s7 ⟨h7, _⟩ => ?_)
  refine WP.seq (WP.mono (h7.widen (k := 8) (a := 25) (by decide) (by decide) (by rd_simp [z]) (by decide)
    (by decide) (live' := [(true, 14), (false, 25), (true, 19), (true, 15), (true, 9)]) (by decide))
    fun s8 ⟨h8, _⟩ => ?_)
  refine WP.seq (WP.block_append (WP.mono h8.len4 fun s9 ⟨h9, c9, _⟩ =>
    WP.mono h9.toWB fun s10 ⟨h10, k10⟩ => ?_))
  have c10 : s10.gpr .r4 = BitVec.ofNat 64 (ww (kK s0) / 2) := by rw [k10.gpr _ (by decide)]; exact c9
  refine WP.mono (h10.mulW (o := 17) (x := 8) (y := 14) (by decide) (by decide) (by decide) (by decide)
    (by decide) c10 (live' := [(true, 8), (true, 14), (false, 25), (true, 19), (true, 15), (true, 9)]) (by decide))
    fun t ht => ⟨_, V, ht.drop (by decide) (by decide), ?_, ?_, by rd_simp [z], by rd_simp, by rd_simp,
      fun _ _ => rfl⟩
  · rd_simp [hb]
  · have eW : wW (kK s0) = 2 * ww (kK s0) + 2 := by have := vw_wide s0; rw [vw_true, vw_false] at this
    have lb : (A false 25 + 1) % 2 ^ (32 * ww (kK s0)) < 2 ^ (32 * vw s0 true) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by decide) (by rw [vw_true, eW]; omega_using []))
    rw [VG.Proof.Rsa.RecoverDet.prod_iter _ _ _ lb]
    rd_simp [hb]

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
