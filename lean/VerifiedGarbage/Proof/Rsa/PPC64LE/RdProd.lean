module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdGcd
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the products

`product_ok`: `32 w` steps of `RecoverDet.prodStep` on the wide multiplier
(array 8), multiplicand (12 or 14) and product (17), through the arrays
11 and 20 and the zero 15; `aProduct_ok`: `a = gcd(u, x) 2^k x`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet (wsub prodStep)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.RecoverDet (product productStep aProduct sB0 sB1 sY)

/-- An addition by two subtractions: `a - (0 - c) = a + c`. -/
theorem wsub_neg {b a c : Nat} (ha : a < 2 ^ b) (hc : c < 2 ^ b) : wsub b a (wsub b 0 c) = (a + c) % 2 ^ b := by
  unfold wsub
  rcases Nat.eq_zero_or_pos c with rfl | pos
  · simp [Nat.mod_eq_of_lt ha]
  · rw [show 0 + 2 ^ b - c = 2 ^ b - c by omega, Nat.mod_eq_of_lt (show 2 ^ b - c < 2 ^ b by omega),
      show a + 2 ^ b - (2 ^ b - c) = a + c by omega]

/-- The arrays a product keeps, but its own: for the first, one and `n`; for the second, one,
`n` (wide) and `b`. -/
abbrev pR (x : Nat) : List (Bool × Nat) :=
  if x = 12 then [(true, 9), (false, 32)] else [(true, 9), (true, 19), (false, 25)]

/-- The arrays of a product: the multiplier, the multiplicand `x`, the product, zero, and `pR x`. -/
abbrev pL (x : Nat) : List (Bool × Nat) := (true, 8) :: (true, x) :: (true, 17) :: (true, 15) :: pR x

section
variable {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat} {ls : List Nat}

/-- A step of a product. -/
theorem productStep_ok {x : Nat} (hx : x = 12 ∨ x = 14) (h : DS s0 true A (pL x) V ls s) (z : A true 15 = 0)
    (hls : ∀ e ∈ ls, e + 4 ≤ sY ∨ sY + 4 ≤ e) :
    WP isa (productStep 8 x 17 11 20 15) s fun t => ∃ A' V', DS s0 true A' (pL x) V' ls t ∧
      (A' true 8, A' true x, A' true 17) = prodStep (32 * vw s0 true) (A true 8, A true x, A true 17) ∧
      A' true 15 = 0 ∧ (∀ e ∈ pR x, A' e.1 e.2 = A e.1 e.2) ∧ (∀ d ∈ ls, V' d = V d) ∧
      t.gpr .r27 = s.gpr .r27 - BitVec.ofNat 64 1 := by
  have lx := h.lt (b' := true) (j := x) (by simp)
  have la := h.lt (b' := true) (j := 17) (by simp)
  rw [vw_true] at lx la
  unfold productStep VG.Impl.Rsa.PPC64LE.RecoverDet.add
  simp only [seqs]
  refine WP.seq (WP.mono (h.bitOfB (j := 8) (sl := sY) (by simp) (by decide) (ls' := ls)
    (fun e he => ⟨he, hls e he⟩)) fun s1 ⟨h1, k1⟩ => ?_)
  refine WP.seq (WP.mono (h1.sel (o := 11) (a := 15) (c := x) (sl := sY) (by rcases hx with rfl | rfl <;> decide) (by rcases hx with rfl | rfl <;> decide) (by rcases hx with rfl | rfl <;> decide)
    (by simp) (by rd_simp; omega) (live' := pL x) (by rcases hx with rfl | rfl <;> decide)) fun s2 ⟨h2, k2⟩ => ?_)
  refine WP.seq ?_
  refine WP.seq (WP.mono (h2.sub3 (o := 20) (a := 15) (c := 11) (by rcases hx with rfl | rfl <;> decide) (by rcases hx with rfl | rfl <;> decide) (by rcases hx with rfl | rfl <;> decide)
    (live' := (true, 11) :: pL x) (by rcases hx with rfl | rfl <;> decide)) fun s3 ⟨h3, _, k3⟩ => ?_)
  refine WP.mono (h3.sub3 (o := 17) (a := 17) (c := 20) (by rcases hx with rfl | rfl <;> decide) (by rcases hx with rfl | rfl <;> decide) (by rcases hx with rfl | rfl <;> decide)
    (live' := [(true, 8), (true, x), (true, 15)] ++ pR x) (by rcases hx with rfl | rfl <;> decide)) fun s4 ⟨h4, _, k4⟩ => ?_
  refine WP.seq (WP.mono (h4.shl (j := x) (by rcases hx with rfl | rfl <;> decide) (live' := [(true, 17), (true, 8), (true, 15)] ++ pR x)
    (by rcases hx with rfl | rfl <;> decide)) fun s5 ⟨h5, _, k5⟩ => ?_)
  refine WP.seq (WP.mono (h5.li9 (v := 0) (by rcases hx with rfl | rfl <;> decide)) fun s6 ⟨h6, r6, k6⟩ => ?_)
  refine WP.seq (WP.mono (h6.half (j := 8) (by rcases hx with rfl | rfl <;> decide) r6 (live' := [(true, x), (true, 17), (true, 15)] ++ pR x)
    (by rcases hx with rfl | rfl <;> decide)) fun s7 ⟨h7, k7⟩ => ?_)
  refine WP.mono h7.next fun t ⟨ht, c, kt⟩ => ⟨_, _, ht.drop (by rcases hx with rfl | rfl <;> decide) (fun d hd => List.mem_cons_of_mem _ hd),
    ?_, ?_, ?_, fun d hd => ?_, ?_⟩
  · have e : wsub (32 * wW (kK s0)) (A true 17) (wsub (32 * wW (kK s0)) 0 (if A true 8 % 2 = 0 then 0 else A true x)) =
        (A true 17 + if A true 8 % 2 = 0 then 0 else A true x) % 2 ^ (32 * wW (kK s0)) :=
      wsub_neg la (by split <;> omega)
    rcases hx with rfl | rfl <;> rd_simp [prodStep, e, z]
  · rcases hx with rfl | rfl <;> rd_simp [z]
  · intro e he
    rcases hx with rfl | rfl
    · simp [pR] at he
      rcases he with rfl | rfl <;> rd_simp
    · simp [pR] at he
      rcases he with rfl | rfl | rfl <;> rd_simp
  · have : d ≠ sY := by have := hls d hd; simp only [sY] at this ⊢; omega
    simp [updV, this]
  · rw [c, k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide),
      k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]

/-- A product: `32 w` steps. -/
theorem product_ok {x : Nat} (hx : x = 12 ∨ x = 14) (h : DS s0 true A (pL x) V ls s) (z : A true 15 = 0)
    (hls : ∀ e ∈ ls, e + 4 ≤ sY ∨ sY + 4 ≤ e) (c : s.gpr .r27 = BitVec.ofNat 64 (32 * ww (kK s0))) :
    WP isa (product 8 x 17 11 20 15) s fun t => ∃ A' V', DS s0 true A' (pL x) V' ls t ∧
      (A' true 8, A' true x, A' true 17) =
        (prodStep (32 * vw s0 true))^[32 * ww (kK s0)] (A true 8, A true x, A true 17) ∧
      A' true 15 = 0 ∧ (∀ e ∈ pR x, A' e.1 e.2 = A e.1 e.2) ∧ (∀ d ∈ ls, V' d = V d) := by
  have w2 := h.base.sz.w2
  have w1 := h.base.sz.w1
  let Inv : Nat → State → Prop := fun i t => ∃ A' V', DS s0 true A' (pL x) V' ls t ∧
    (A' true 8, A' true x, A' true 17) = (prodStep (32 * vw s0 true))^[i] (A true 8, A true x, A true 17) ∧
    A' true 15 = 0 ∧ (∀ e ∈ pR x, A' e.1 e.2 = A e.1 e.2) ∧ (∀ d ∈ ls, V' d = V d)
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (body := productStep 8 x 17 11 20 15) (cnt := .r27)
    (N := 32 * ww (kK s0)) (by omega) (by omega) Inv
    (fun i _ t ⟨A', V', ht, e, z', r, v⟩ _ => ?_) ⟨A, V, h, rfl, z, fun _ _ => rfl, fun _ _ => rfl⟩ c
  refine WP.mono (productStep_ok hx ht z' hls) fun t' ⟨A'', V'', ht', e', z'', r', v', c'⟩ =>
    ⟨⟨A'', V'', ht', ?_, z'', fun e he => (r' e he).trans (r e he), fun d hd => (v' d hd).trans (v d hd)⟩, c'⟩
  rw [e', Function.iterate_succ_apply', ← e]

/-- `a = gcd(u, x) 2^k x` modulo `2^(32 W)`, from the GCD in the wide `wY` and `2^k x` in `wX3`. -/
theorem aProduct_ok (h : DS s0 false A [(true, 8), (true, 12), (true, 15), (true, 9), (false, 32)] V [sB1, sB0] s)
    (z : A true 15 = 0) :
    WP isa aProduct s fun t => ∃ A' V', DS s0 true A' (pL 12) V' [sB1, sB0] t ∧
      A' true 17 = ((prodStep (32 * vw s0 true))^[32 * ww (kK s0)] (A true 8, A true 12, 0)).2.2 ∧
      A' true 15 = 0 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧ V' sB0 = V sB0 ∧ V' sB1 = V sB1 := by
  unfold aProduct
  simp only [seqs]
  refine WP.seq (WP.block_append (WP.mono h.countN fun s1 ⟨h1, c1, _⟩ =>
    WP.mono h1.toWB fun s2 ⟨h2, k2⟩ => ?_))
  have c2 : s2.gpr .r27 = BitVec.ofNat 64 (32 * ww (kK s0)) := by rw [k2.gpr _ (by decide)]; exact c1
  refine WP.seq (WP.mono (h2.copy (o := 17) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(true, 8), (true, 12), (true, 15), (true, 9), (false, 32)]) (by decide)) fun s3 ⟨h3, k3, _⟩ => ?_)
  show WP isa (product 8 12 17 11 20 15) s3 _
  refine WP.mono (product_ok (x := 12) (ls := [sB1, sB0]) (.inl rfl) (h3.drop (by decide) (by decide)) (by rd_simp [z])
    (by decide)
    (by rw [k3.gpr _ (by decide)]; exact c2)) fun t ⟨A', V', ht, e, z', r, v⟩ =>
      ⟨A', V', ht, ?_, z', ?_, ?_, v _ (by decide), v _ (by decide)⟩
  · have e3 : (upd A true 17 (A true 15) true 8, upd A true 17 (A true 15) true 12, upd A true 17 (A true 15) true 17) =
        (A true 8, A true 12, 0) := by rd_simp [z]
    rw [← e3, ← e]
  · rw [r (true, 9) (by decide)]; rd_simp
  · rw [r (false, 32) (by decide)]; rd_simp

end

end VG.Proof.Rsa.PPC64LE.RecDet
