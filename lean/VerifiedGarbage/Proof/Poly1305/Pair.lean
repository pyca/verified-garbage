import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq
import VerifiedGarbage.Proof.Poly1305.Stream

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.Horner`. -/
section

/-!
# Poly1305: Horner's rule in four lanes

A vector implementation can absorb four blocks at a time in four lanes: lane
`k` holds `V_k`, and a group of blocks `m₀ … m₃` makes it `(V_k + m_k) r⁴`; at
the end, the last group makes it `(V_k + m_k) r^(4-k)` and the lanes are
summed. With `S = r⁴ V₀ + r³ V₁ + r² V₂ + r V₃`, the invariant is `S ≡ r⁴ a`
for the accumulator `a` of the blocks so far (starting with `V₀ = a`, the
others 0).
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (P leNum)

/-- The value of a block with its `0x01` byte appended. -/
abbrev mv (b : List Byte) : Nat := leNum (b ++ [0x01])

theorem mod_step {x y : Nat} (r v : Nat) (h : x ≡ y [MOD P]) : r * (x + v) % P ≡ r * (y + v) [MOD P] :=
  (Nat.mod_modEq _ _).trans ((h.add_right v).mul_left r)

theorem absorbAll_four {r a : Nat} {b0 b1 b2 b3 : List Byte} (h0 : b0.length = 16) (h1 : b1.length = 16)
    (h2 : b2.length = 16) (h3 : b3.length = 16) :
    absorbAll r a (b0 ++ b1 ++ b2 ++ b3) ≡
      r ^ 4 * a + r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3 [MOD P] := by
  have l0 : (b0 ++ b1).length % 16 = 0 := by simp [h0, h1]
  have l1 : (b0 ++ b1 ++ b2).length % 16 = 0 := by simp [h0, h1, h2]
  rw [absorbAll_append l1, absorbAll_append l0, absorbAll_append (by omega),
    absorbAll_block (by omega) (by omega), absorbAll_block (by omega) (by omega),
    absorbAll_block (by omega) (by omega), absorbAll_block (by omega) (by omega)]
  refine (VG.Proof.Poly1305.mod_step r _ (VG.Proof.Poly1305.mod_step r _ (VG.Proof.Poly1305.mod_step r _ (Nat.mod_modEq _ _)))).trans ?_
  rw [show r * (r * (r * (r * (a + VG.Proof.Poly1305.mv b0) + VG.Proof.Poly1305.mv b1) + VG.Proof.Poly1305.mv b2) + VG.Proof.Poly1305.mv b3) =
    r ^ 4 * a + r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3 by ring]

/-- The lanes' sum, weighted by the powers of `r` of the last group. -/
abbrev lanes (r V0 V1 V2 V3 : Nat) : Nat := r ^ 4 * V0 + r ^ 3 * V1 + r ^ 2 * V2 + r * V3

section
variable {r X V0 V1 V2 V3 W0 W1 W2 W3 : Nat} {b0 b1 b2 b3 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (hS : VG.Proof.Poly1305.lanes r V0 V1 V2 V3 ≡ r ^ 4 * X [MOD P])
include h0 h1 h2 h3 hS

/-- A group of four blocks, each lane multiplied by `r⁴`. -/
theorem horner_step (e0 : W0 ≡ (V0 + VG.Proof.Poly1305.mv b0) * r ^ 4 [MOD P]) (e1 : W1 ≡ (V1 + VG.Proof.Poly1305.mv b1) * r ^ 4 [MOD P])
    (e2 : W2 ≡ (V2 + VG.Proof.Poly1305.mv b2) * r ^ 4 [MOD P]) (e3 : W3 ≡ (V3 + VG.Proof.Poly1305.mv b3) * r ^ 4 [MOD P]) :
    VG.Proof.Poly1305.lanes r W0 W1 W2 W3 ≡ r ^ 4 * absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := by
  have hA := (VG.Proof.Poly1305.absorbAll_four (r := r) (a := X) h0 h1 h2 h3).mul_left (r ^ 4)
  have hL : VG.Proof.Poly1305.lanes r W0 W1 W2 W3 ≡ r ^ 4 * (VG.Proof.Poly1305.lanes r V0 V1 V2 V3 +
      (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3)) [MOD P] := by
    refine ((((e0.mul_left _).add (e1.mul_left _)).add (e2.mul_left _)).add (e3.mul_left _)).trans ?_
    rw [show r ^ 4 * ((V0 + VG.Proof.Poly1305.mv b0) * r ^ 4) + r ^ 3 * ((V1 + VG.Proof.Poly1305.mv b1) * r ^ 4) +
        r ^ 2 * ((V2 + VG.Proof.Poly1305.mv b2) * r ^ 4) + r * ((V3 + VG.Proof.Poly1305.mv b3) * r ^ 4) =
        r ^ 4 * (VG.Proof.Poly1305.lanes r V0 V1 V2 V3 + (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3)) by
      simp only [VG.Proof.Poly1305.lanes]; ring]
  calc VG.Proof.Poly1305.lanes r W0 W1 W2 W3
      _ ≡ r ^ 4 * (VG.Proof.Poly1305.lanes r V0 V1 V2 V3 +
          (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3)) [MOD P] := hL
      _ ≡ r ^ 4 * (r ^ 4 * X + (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3)) [MOD P] :=
        (hS.add_right _).mul_left _
      _ = r ^ 4 * (r ^ 4 * X + r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3) := by ring
      _ ≡ r ^ 4 * absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := hA.symm

/-- The last group, lane `k` multiplied by `r^(4-k)`, and the lanes summed. -/
theorem horner_last (e0 : W0 ≡ (V0 + VG.Proof.Poly1305.mv b0) * r ^ 4 [MOD P]) (e1 : W1 ≡ (V1 + VG.Proof.Poly1305.mv b1) * r ^ 3 [MOD P])
    (e2 : W2 ≡ (V2 + VG.Proof.Poly1305.mv b2) * r ^ 2 [MOD P]) (e3 : W3 ≡ (V3 + VG.Proof.Poly1305.mv b3) * r [MOD P]) :
    W0 + W1 + W2 + W3 ≡ absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := by
  have hA := VG.Proof.Poly1305.absorbAll_four (r := r) (a := X) h0 h1 h2 h3
  refine (((e0.add e1).add e2).add e3).trans ?_
  rw [show (V0 + VG.Proof.Poly1305.mv b0) * r ^ 4 + (V1 + VG.Proof.Poly1305.mv b1) * r ^ 3 + (V2 + VG.Proof.Poly1305.mv b2) * r ^ 2 + (V3 + VG.Proof.Poly1305.mv b3) * r =
    VG.Proof.Poly1305.lanes r V0 V1 V2 V3 + (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3) by
      simp only [VG.Proof.Poly1305.lanes]; ring]
  calc VG.Proof.Poly1305.lanes r V0 V1 V2 V3 + (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3)
      _ ≡ r ^ 4 * X + (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3) [MOD P] :=
        hS.add_right _
      _ = r ^ 4 * X + r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3 := by ring
      _ ≡ absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := hA.symm

end

end VG.Proof.Poly1305

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.Horner8`. -/
section

/-!
# Poly1305: Horner's rule in eight lanes

As `Horner.lean`, with eight lanes: lane `j` holds `V_j`, a group of blocks
`m₀ … m₇` makes it `(V_j + m_j) r⁸`, and the last group `(V_j + m_j) r^(8-j)`,
after which the lanes are summed. With `S = r⁸ V₀ + r⁷ V₁ + … + r V₇`, the
invariant is `S ≡ r⁸ a` for the accumulator `a` of the blocks so far.
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (P leNum)

section
variable {r a : Nat} {b0 b1 b2 b3 b4 b5 b6 b7 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (h4 : b4.length = 16) (h5 : b5.length = 16) (h6 : b6.length = 16) (h7 : b7.length = 16)
include h0 h1 h2 h3 h4 h5 h6 h7

theorem absorbAll_eight :
    absorbAll r a (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) ≡
      r ^ 8 * a + r ^ 8 * VG.Proof.Poly1305.mv b0 + r ^ 7 * VG.Proof.Poly1305.mv b1 + r ^ 6 * VG.Proof.Poly1305.mv b2 + r ^ 5 * VG.Proof.Poly1305.mv b3 + r ^ 4 * VG.Proof.Poly1305.mv b4 +
        r ^ 3 * VG.Proof.Poly1305.mv b5 + r ^ 2 * VG.Proof.Poly1305.mv b6 + r * VG.Proof.Poly1305.mv b7 [MOD P] := by
  have l : (b0 ++ b1 ++ b2 ++ b3).length % 16 = 0 := by simp [h0, h1, h2, h3]
  rw [show b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 = (b0 ++ b1 ++ b2 ++ b3) ++ (b4 ++ b5 ++ b6 ++ b7) by
    simp only [List.append_assoc], absorbAll_append l]
  refine (VG.Proof.Poly1305.absorbAll_four h4 h5 h6 h7).trans ?_
  have hA := VG.Proof.Poly1305.absorbAll_four (r := r) (a := a) h0 h1 h2 h3
  refine ((((hA.mul_left (r ^ 4)).add_right _).add_right _).add_right _).add_right _ |>.trans ?_
  rw [show r ^ 4 * (r ^ 4 * a + r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3) + r ^ 4 * VG.Proof.Poly1305.mv b4 +
      r ^ 3 * VG.Proof.Poly1305.mv b5 + r ^ 2 * VG.Proof.Poly1305.mv b6 + r * VG.Proof.Poly1305.mv b7 =
    r ^ 8 * a + r ^ 8 * VG.Proof.Poly1305.mv b0 + r ^ 7 * VG.Proof.Poly1305.mv b1 + r ^ 6 * VG.Proof.Poly1305.mv b2 + r ^ 5 * VG.Proof.Poly1305.mv b3 + r ^ 4 * VG.Proof.Poly1305.mv b4 +
      r ^ 3 * VG.Proof.Poly1305.mv b5 + r ^ 2 * VG.Proof.Poly1305.mv b6 + r * VG.Proof.Poly1305.mv b7 by ring]

end

/-- The lanes' sum, weighted by the powers of `r` of the last group. -/
abbrev lanes8 (r V0 V1 V2 V3 V4 V5 V6 V7 : Nat) : Nat :=
  r ^ 8 * V0 + r ^ 7 * V1 + r ^ 6 * V2 + r ^ 5 * V3 + r ^ 4 * V4 + r ^ 3 * V5 + r ^ 2 * V6 + r * V7

/-- The weighted values of a group's blocks. -/
abbrev msum8 (r : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : List Byte) : Nat :=
  r ^ 8 * VG.Proof.Poly1305.mv b0 + r ^ 7 * VG.Proof.Poly1305.mv b1 + r ^ 6 * VG.Proof.Poly1305.mv b2 + r ^ 5 * VG.Proof.Poly1305.mv b3 + r ^ 4 * VG.Proof.Poly1305.mv b4 + r ^ 3 * VG.Proof.Poly1305.mv b5 +
    r ^ 2 * VG.Proof.Poly1305.mv b6 + r * VG.Proof.Poly1305.mv b7

section
variable {r X V0 V1 V2 V3 V4 V5 V6 V7 W0 W1 W2 W3 W4 W5 W6 W7 : Nat}
  {b0 b1 b2 b3 b4 b5 b6 b7 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (h4 : b4.length = 16) (h5 : b5.length = 16) (h6 : b6.length = 16) (h7 : b7.length = 16)
  (hS : VG.Proof.Poly1305.lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 ≡ r ^ 8 * X [MOD P])
include h0 h1 h2 h3 h4 h5 h6 h7 hS

omit hS in
theorem absorbAll_eight' :
    absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) ≡
      r ^ 8 * X + VG.Proof.Poly1305.msum8 r b0 b1 b2 b3 b4 b5 b6 b7 [MOD P] := by
  refine (VG.Proof.Poly1305.absorbAll_eight h0 h1 h2 h3 h4 h5 h6 h7).trans ?_
  rw [show r ^ 8 * X + r ^ 8 * VG.Proof.Poly1305.mv b0 + r ^ 7 * VG.Proof.Poly1305.mv b1 + r ^ 6 * VG.Proof.Poly1305.mv b2 + r ^ 5 * VG.Proof.Poly1305.mv b3 + r ^ 4 * VG.Proof.Poly1305.mv b4 +
      r ^ 3 * VG.Proof.Poly1305.mv b5 + r ^ 2 * VG.Proof.Poly1305.mv b6 + r * VG.Proof.Poly1305.mv b7 = r ^ 8 * X + VG.Proof.Poly1305.msum8 r b0 b1 b2 b3 b4 b5 b6 b7 by
    simp only [VG.Proof.Poly1305.msum8]; ring]

/-- A group of eight blocks, each lane multiplied by `r⁸`. -/
theorem horner8_step (e0 : W0 ≡ (V0 + VG.Proof.Poly1305.mv b0) * r ^ 8 [MOD P]) (e1 : W1 ≡ (V1 + VG.Proof.Poly1305.mv b1) * r ^ 8 [MOD P])
    (e2 : W2 ≡ (V2 + VG.Proof.Poly1305.mv b2) * r ^ 8 [MOD P]) (e3 : W3 ≡ (V3 + VG.Proof.Poly1305.mv b3) * r ^ 8 [MOD P])
    (e4 : W4 ≡ (V4 + VG.Proof.Poly1305.mv b4) * r ^ 8 [MOD P]) (e5 : W5 ≡ (V5 + VG.Proof.Poly1305.mv b5) * r ^ 8 [MOD P])
    (e6 : W6 ≡ (V6 + VG.Proof.Poly1305.mv b6) * r ^ 8 [MOD P]) (e7 : W7 ≡ (V7 + VG.Proof.Poly1305.mv b7) * r ^ 8 [MOD P]) :
    VG.Proof.Poly1305.lanes8 r W0 W1 W2 W3 W4 W5 W6 W7 ≡
      r ^ 8 * absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) [MOD P] := by
  have hA := (VG.Proof.Poly1305.absorbAll_eight' (r := r) (X := X) h0 h1 h2 h3 h4 h5 h6 h7).mul_left (r ^ 8)
  have hL : VG.Proof.Poly1305.lanes8 r W0 W1 W2 W3 W4 W5 W6 W7 ≡
      r ^ 8 * (VG.Proof.Poly1305.lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + VG.Proof.Poly1305.msum8 r b0 b1 b2 b3 b4 b5 b6 b7) [MOD P] := by
    refine ((((((((e0.mul_left _).add (e1.mul_left _)).add (e2.mul_left _)).add (e3.mul_left _)).add
      (e4.mul_left _)).add (e5.mul_left _)).add (e6.mul_left _)).add (e7.mul_left _)).trans ?_
    rw [show r ^ 8 * ((V0 + VG.Proof.Poly1305.mv b0) * r ^ 8) + r ^ 7 * ((V1 + VG.Proof.Poly1305.mv b1) * r ^ 8) +
        r ^ 6 * ((V2 + VG.Proof.Poly1305.mv b2) * r ^ 8) + r ^ 5 * ((V3 + VG.Proof.Poly1305.mv b3) * r ^ 8) + r ^ 4 * ((V4 + VG.Proof.Poly1305.mv b4) * r ^ 8) +
        r ^ 3 * ((V5 + VG.Proof.Poly1305.mv b5) * r ^ 8) + r ^ 2 * ((V6 + VG.Proof.Poly1305.mv b6) * r ^ 8) + r * ((V7 + VG.Proof.Poly1305.mv b7) * r ^ 8) =
        r ^ 8 * (VG.Proof.Poly1305.lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + VG.Proof.Poly1305.msum8 r b0 b1 b2 b3 b4 b5 b6 b7) by
      simp only [VG.Proof.Poly1305.lanes8, VG.Proof.Poly1305.msum8]; ring]
  exact hL.trans (((hS.add_right _).mul_left _).trans hA.symm)

/-- The last group, lane `j` multiplied by `r^(8-j)`, and the lanes summed. -/
theorem horner8_last (e0 : W0 ≡ (V0 + VG.Proof.Poly1305.mv b0) * r ^ 8 [MOD P]) (e1 : W1 ≡ (V1 + VG.Proof.Poly1305.mv b1) * r ^ 7 [MOD P])
    (e2 : W2 ≡ (V2 + VG.Proof.Poly1305.mv b2) * r ^ 6 [MOD P]) (e3 : W3 ≡ (V3 + VG.Proof.Poly1305.mv b3) * r ^ 5 [MOD P])
    (e4 : W4 ≡ (V4 + VG.Proof.Poly1305.mv b4) * r ^ 4 [MOD P]) (e5 : W5 ≡ (V5 + VG.Proof.Poly1305.mv b5) * r ^ 3 [MOD P])
    (e6 : W6 ≡ (V6 + VG.Proof.Poly1305.mv b6) * r ^ 2 [MOD P]) (e7 : W7 ≡ (V7 + VG.Proof.Poly1305.mv b7) * r [MOD P]) :
    W0 + W1 + W2 + W3 + W4 + W5 + W6 + W7 ≡
      absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) [MOD P] := by
  have hA := VG.Proof.Poly1305.absorbAll_eight' (r := r) (X := X) h0 h1 h2 h3 h4 h5 h6 h7
  refine (((((((e0.add e1).add e2).add e3).add e4).add e5).add e6).add e7).trans ?_
  rw [show (V0 + VG.Proof.Poly1305.mv b0) * r ^ 8 + (V1 + VG.Proof.Poly1305.mv b1) * r ^ 7 + (V2 + VG.Proof.Poly1305.mv b2) * r ^ 6 + (V3 + VG.Proof.Poly1305.mv b3) * r ^ 5 +
      (V4 + VG.Proof.Poly1305.mv b4) * r ^ 4 + (V5 + VG.Proof.Poly1305.mv b5) * r ^ 3 + (V6 + VG.Proof.Poly1305.mv b6) * r ^ 2 + (V7 + VG.Proof.Poly1305.mv b7) * r =
      VG.Proof.Poly1305.lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + VG.Proof.Poly1305.msum8 r b0 b1 b2 b3 b4 b5 b6 b7 by
    simp only [VG.Proof.Poly1305.lanes8, VG.Proof.Poly1305.msum8]; ring]
  exact (hS.add_right _).trans hA.symm

end

end VG.Proof.Poly1305

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.Pair`. -/
section

/-!
# Poly1305: Horner's rule in two lanes of two blocks

The arithmetic of AArch64's AdvSIMD `update` (`Impl/Poly1305/AArch64/Vector.lean`),
as Nat identities. Two lanes `A` and `B` absorb a group of four blocks
`m₀ … m₃` as `A ← (A + m₀) r⁴ + m₂ r²` and `B ← (B + m₁) r⁴ + m₃ r²`, which
keeps `A r + B ≡ r a` for the accumulator `a` of the blocks so far (starting
with `A = a`, `B = 0`); the last group multiplies `B + m₁` by `r³` and `m₃` by
`r`, after which `A + B ≡ a`.

The products of five 26-bit limbs, `d_k = Σ_{i ≤ k} x_i y_(k-i) + Σ_{i > k}
x_i (5 y)_(k+5-i)`, are `Limbs26.pd`'s; they are carried in two interleaved
chains (`carry`), and the limbs of the sum of the lanes are put back into
three 64-bit words (`pack`) whose third is then reduced (`fold6`).
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (P leNum)
open Limbs26 (val P_eq)

/-! ## Horner's rule in two lanes -/

section
variable {r X A B A' B' : Nat} {b0 b1 b2 b3 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (hS : A * r + B ≡ r * X [MOD P])
include h0 h1 h2 h3 hS

/-- A group of four blocks. -/
theorem pair_step (eA : A' ≡ (A + VG.Proof.Poly1305.mv b0) * r ^ 4 + VG.Proof.Poly1305.mv b2 * r ^ 2 [MOD P])
    (eB : B' ≡ (B + VG.Proof.Poly1305.mv b1) * r ^ 4 + VG.Proof.Poly1305.mv b3 * r ^ 2 [MOD P]) :
    A' * r + B' ≡ r * absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := by
  have hA := (VG.Proof.Poly1305.absorbAll_four (r := r) (a := X) h0 h1 h2 h3).mul_left r
  calc A' * r + B'
      _ ≡ ((A + VG.Proof.Poly1305.mv b0) * r ^ 4 + VG.Proof.Poly1305.mv b2 * r ^ 2) * r + ((B + VG.Proof.Poly1305.mv b1) * r ^ 4 + VG.Proof.Poly1305.mv b3 * r ^ 2) [MOD P] :=
        (eA.mul_right r).add eB
      _ = r ^ 4 * (A * r + B) + r * (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3) := by
        ring
      _ ≡ r ^ 4 * (r * X) + r * (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3) [MOD P] :=
        (hS.mul_left _).add_right _
      _ = r * (r ^ 4 * X + r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3) := by ring
      _ ≡ r * absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := hA.symm

/-- The last group: then `A' + B'` is the accumulator. -/
theorem pair_last (eA : A' ≡ (A + VG.Proof.Poly1305.mv b0) * r ^ 4 + VG.Proof.Poly1305.mv b2 * r ^ 2 [MOD P])
    (eB : B' ≡ (B + VG.Proof.Poly1305.mv b1) * r ^ 3 + VG.Proof.Poly1305.mv b3 * r [MOD P]) :
    A' + B' ≡ absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := by
  have hA := VG.Proof.Poly1305.absorbAll_four (r := r) (a := X) h0 h1 h2 h3
  calc A' + B'
      _ ≡ ((A + VG.Proof.Poly1305.mv b0) * r ^ 4 + VG.Proof.Poly1305.mv b2 * r ^ 2) + ((B + VG.Proof.Poly1305.mv b1) * r ^ 3 + VG.Proof.Poly1305.mv b3 * r) [MOD P] := eA.add eB
      _ = r ^ 3 * (A * r + B) + (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3) := by ring
      _ ≡ r ^ 3 * (r * X) + (r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3) [MOD P] :=
        (hS.mul_left _).add_right _
      _ = r ^ 4 * X + r ^ 4 * VG.Proof.Poly1305.mv b0 + r ^ 3 * VG.Proof.Poly1305.mv b1 + r ^ 2 * VG.Proof.Poly1305.mv b2 + r * VG.Proof.Poly1305.mv b3 := by ring
      _ ≡ absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := hA.symm

end

/-- The lanes start as the accumulator and 0. -/
theorem pair_init (r X : Nat) : X * r + 0 ≡ r * X [MOD P] := by
  rw [Nat.add_zero, Nat.mul_comm]

/-- Absorbing from congruent accumulators gives congruent results. -/
theorem absorbAll_congr {r a a' : Nat} (h : a ≡ a' [MOD P]) (msg : List Byte) :
    absorbAll r a msg ≡ absorbAll r a' msg [MOD P] := by
  unfold absorbAll
  generalize List.range (Spec.Poly1305.numBlocks msg) = l
  cases l with
  | nil => exact h
  | cons i l =>
    simp only [List.foldl_cons]
    rw [show r * (a + leNum (Spec.Poly1305.block msg i ++ [0x01])) % P =
      r * (a' + leNum (Spec.Poly1305.block msg i ++ [0x01])) % P from (h.add_right _).mul_left r]

namespace Pair

/-! ## Products -/

/-- The multiplier of limb `i` of the operand in `d_k`: `y` or `5 y`. -/
def mulL (y : Nat → Nat) (i k : Nat) : Nat := if i ≤ k then y (k - i) else 5 * y (k + 5 - i)

/-- `d_k`, summed in the order of the limbs of the operand. -/
def prod (x y : Nat → Nat) (k : Nat) : Nat :=
  x 0 * VG.Proof.Poly1305.Pair.mulL y 0 k + x 1 * VG.Proof.Poly1305.Pair.mulL y 1 k + x 2 * VG.Proof.Poly1305.Pair.mulL y 2 k + x 3 * VG.Proof.Poly1305.Pair.mulL y 3 k + x 4 * VG.Proof.Poly1305.Pair.mulL y 4 k

theorem prod_val (x y : Nat → Nat) : val (VG.Proof.Poly1305.Pair.prod x y) + P * Limbs26.pc x y = val x * val y := by
  simp only [val, VG.Proof.Poly1305.Pair.prod, VG.Proof.Poly1305.Pair.mulL, Limbs26.pc, P_eq, Nat.reduceLeDiff, ite_true, ite_false, Nat.reduceSub,
    Nat.reduceAdd, Nat.le_refl, Nat.zero_le]
  ring

theorem prod_mod (x y : Nat → Nat) : val (VG.Proof.Poly1305.Pair.prod x y) ≡ val x * val y [MOD P] := by
  have h := VG.Proof.Poly1305.Pair.prod_val x y
  calc val (VG.Proof.Poly1305.Pair.prod x y) ≡ val (VG.Proof.Poly1305.Pair.prod x y) + P * Limbs26.pc x y [MOD P] :=
        (Nat.add_mul_mod_self_left _ _ _).symm
    _ = val x * val y := h

/-! ## Carrying -/

section
variable (d : Nat → Nat)

/-- The two chains, `d₀ → d₁ → d₂ → d₃` and `d₃ → d₄ → d₀ → d₁`, as the code
interleaves them. -/
def d1a : Nat := d 1 + d 0 / 2 ^ 26
def d4a : Nat := d 4 + d 3 / 2 ^ 26
def d2a : Nat := d 2 + VG.Proof.Poly1305.Pair.d1a d / 2 ^ 26
def h0b : Nat := d 0 % 2 ^ 26 + VG.Proof.Poly1305.Pair.d4a d / 2 ^ 26 + VG.Proof.Poly1305.Pair.d4a d / 2 ^ 26 * 2 ^ 2
def h3b : Nat := d 3 % 2 ^ 26 + VG.Proof.Poly1305.Pair.d2a d / 2 ^ 26

/-- The limbs after carrying. -/
def carry : Nat → Nat
  | 0 => VG.Proof.Poly1305.Pair.h0b d % 2 ^ 26
  | 1 => VG.Proof.Poly1305.Pair.d1a d % 2 ^ 26 + VG.Proof.Poly1305.Pair.h0b d / 2 ^ 26
  | 2 => VG.Proof.Poly1305.Pair.d2a d % 2 ^ 26
  | 3 => VG.Proof.Poly1305.Pair.h3b d % 2 ^ 26
  | _ => VG.Proof.Poly1305.Pair.d4a d % 2 ^ 26 + VG.Proof.Poly1305.Pair.h3b d / 2 ^ 26

end

theorem carry_val (d : Nat → Nat) : val (VG.Proof.Poly1305.Pair.carry d) + P * (VG.Proof.Poly1305.Pair.d4a d / 2 ^ 26) = val d := by
  simp only [val, VG.Proof.Poly1305.Pair.carry, VG.Proof.Poly1305.Pair.h0b, VG.Proof.Poly1305.Pair.h3b, VG.Proof.Poly1305.Pair.d2a, VG.Proof.Poly1305.Pair.d1a, VG.Proof.Poly1305.Pair.d4a, P_eq]
  omega

theorem carry_mod (d : Nat → Nat) : val (VG.Proof.Poly1305.Pair.carry d) ≡ val d [MOD P] := by
  have h := VG.Proof.Poly1305.Pair.carry_val d
  calc val (VG.Proof.Poly1305.Pair.carry d) ≡ val (VG.Proof.Poly1305.Pair.carry d) + P * (VG.Proof.Poly1305.Pair.d4a d / 2 ^ 26) [MOD P] :=
        (Nat.add_mul_mod_self_left _ _ _).symm
    _ = val d := h

theorem carry_congr {d d' : Nat → Nat} (h : ∀ k < 5, d k = d' k) (i : Nat) : VG.Proof.Poly1305.Pair.carry d i = VG.Proof.Poly1305.Pair.carry d' i := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide)
  rcases i with _ | _ | _ | _ | _ <;> simp only [VG.Proof.Poly1305.Pair.carry, VG.Proof.Poly1305.Pair.h0b, VG.Proof.Poly1305.Pair.h3b, VG.Proof.Poly1305.Pair.d2a, VG.Proof.Poly1305.Pair.d1a, VG.Proof.Poly1305.Pair.d4a, h0, h1, h2, h3, h4]

/-- Products below `2⁶²` carry into limbs below `2²⁷`. -/
theorem carry_lt {d : Nat → Nat} (h : ∀ k < 5, d k < 2 ^ 62) : ∀ i < 5, VG.Proof.Poly1305.Pair.carry d i < 2 ^ 27 := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide)
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.Poly1305.Pair.carry, VG.Proof.Poly1305.Pair.h0b, VG.Proof.Poly1305.Pair.h3b, VG.Proof.Poly1305.Pair.d2a, VG.Proof.Poly1305.Pair.d1a, VG.Proof.Poly1305.Pair.d4a] <;> omega

/-! ## Bounds of the products -/

/-- Operands below `2²⁸` and multipliers below `2²⁷` (so `5 y` below
`2³⁰`): each `d_k` is below `2⁶⁰`, and a sum of two below `2⁶¹`. -/
theorem prod_lt {x y : Nat → Nat} (hx : ∀ i < 5, x i < 2 ^ 28) (hy : ∀ i < 5, y i < 2 ^ 27) :
    ∀ k < 5, VG.Proof.Poly1305.Pair.prod x y k < 2 ^ 60 := by
  have hm : ∀ i < 5, ∀ k < 5, VG.Proof.Poly1305.Pair.mulL y i k < 5 * 2 ^ 27 := by
    intro i hi k hk
    simp only [VG.Proof.Poly1305.Pair.mulL]
    split
    · have := hy (k - i) (by omega); omega
    · have := hy (k + 5 - i) (by omega); omega
  intro k hk
  have t : ∀ i < 5, x i * VG.Proof.Poly1305.Pair.mulL y i k < 2 ^ 28 * (5 * 2 ^ 27) := fun i hi =>
    Nat.mul_lt_mul'' (hx i hi) (hm i hi k hk)
  have := t 0 (by decide); have := t 1 (by decide); have := t 2 (by decide)
  have := t 3 (by decide); have := t 4 (by decide)
  simp only [VG.Proof.Poly1305.Pair.prod]
  omega

end Pair

end VG.Proof.Poly1305

end
