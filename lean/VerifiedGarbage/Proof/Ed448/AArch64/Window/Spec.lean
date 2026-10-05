import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.AArch64.Window.KLoop
import VerifiedGarbage.Proof.X448.BaseAdd
import Mathlib.Tactic.Abel

/-!
# Ed448 verification on AArch64: the equation, by the group law

Untrusted: everything here is checked by Lean. The table's entries represent
`[e]P` (`tabPts_rep`), the windows `[k]P` for the challenge `k`
(`winQ_rep`), and so, when `A` and `R` decode, the specification's
`verifyEquation` is `S < L` and the projective comparison of `[4]([S]B +
[k](-A))` with `[4]R` (`verifyEquation_eq`), which the code computes.
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG.Proof.Ed448 (Rep dZ double double_rep identity_rep pointMul_rep pointAdd_rep pointEqual_rep
  decodePoint_rep baseAff basePoint_rep)
open VG.Proof.EdwardsLaw (EPoint)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt addPt_rep)

theorem tabPts_rep {P : Point} {a : EPoint dZ} (h : Rep P a) : ∀ e, Rep (tabPts P e) (e • a)
  | 0 => by rw [zero_smul]; exact identity_rep
  | 1 => by rw [one_smul]; exact h
  | e + 2 => by
    rw [tabPts_succ, show (e + 2) • a = (e + 1) • a + a from succ_nsmul _ _]
    exact addPt_rep (tabPts_rep h (e + 1)) h

theorem dbl4_rep {Q : Point} {a : EPoint dZ} (h : Rep Q a) : Rep (dbl4 Q) ((16 : Nat) • a) := by
  have := double_rep (double_rep (double_rep (double_rep h)))
  rw [show (16 : Nat) • a = a + a + (a + a) + (a + a + (a + a)) + (a + a + (a + a) + (a + a + (a + a))) by abel]
  exact this

theorem wstep_rep {P Q : Point} {a : EPoint dZ} (hP : Rep P a) {q : Nat} (hQ : Rep Q (q • a)) (n : Nat) :
    Rep (wstep P Q n) ((16 * q + n) • a) := by
  have := addPt_rep (dbl4_rep hQ) (tabPts_rep hP n)
  rw [smul_smul, ← add_smul] at this
  exact this

/-- The top `m` bytes of the challenge, as a number. -/
def topVal (b : Nat → BitVec 8) : Nat → Nat
  | 0 => 0
  | m + 1 => 256 * topVal b m + (b (56 - m)).toNat

theorem nib_split (x : BitVec 8) (q : Nat) :
    16 * (16 * q + nibOf x 4) + nibOf x 0 = 256 * q + x.toNat := by
  simp only [nibOf, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem winQ_rep {P : Point} {a : EPoint dZ} (hP : Rep P a) (b : Nat → BitVec 8) :
    ∀ m, Rep (winQ P b m) (topVal b m • a)
  | 0 => by rw [topVal, zero_smul]; exact identity_rep
  | m + 1 => by
    have := wstep_rep hP (wstep_rep hP (winQ_rep hP b m) (nibOf (b (56 - m)) 4)) (nibOf (b (56 - m)) 0)
    rw [nib_split] at this
    exact this

/-- The top bytes of a list of 57, as `decodeLE` reads them. -/
theorem topVal_eq (l : List Byte) (hl : l.length = 57) (b : Nat → BitVec 8) (hb : ∀ i (h : i < 57), b i = l[i]) :
    ∀ m ≤ 57, topVal b m = Spec.Ed448.decodeLE (l.drop (57 - m))
  | 0, _ => by rw [topVal, Nat.sub_zero, List.drop_of_length_le (Nat.le_of_eq hl)]; rfl
  | m + 1, hm => by
    rw [topVal, topVal_eq l hl b hb m (by omega), show 57 - (m + 1) = 56 - m by omega,
      List.drop_eq_getElem_cons (i := 56 - m) (by rw [hl]; omega), show 56 - m + 1 = 57 - m by omega,
      Spec.Ed448.decodeLE, hb (56 - m) (by omega)]
    omega

/-- `4 (x + y) = 4 z` exactly when `4 x = 4 z + 4 (-y)`. -/
theorem four_iff (x y z : EPoint dZ) :
    x + y + (x + y) + (x + y + (x + y)) = z + z + (z + z) ↔
      (4 : Nat) • x = (4 : Nat) • z + (4 : Nat) • (-y) := by
  have e1 : x + y + (x + y) + (x + y + (x + y)) = (4 : Nat) • x + (4 : Nat) • y := by abel
  have e2 : z + z + (z + z) = (4 : Nat) • z := by abel
  rw [e1, e2, smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]

/-- **The equation**, when `A` and `R` decode: `S < L`, and `[4]([S]B + [k](-A))` and `[4]R`
compared projectively, for `[S]B` represented by `SB` and the windows over the challenge's bytes. -/
theorem verifyEquation_eq {pk sig ch : List Byte} (hpk : pk.length = 57) (hsig : sig.length = 114)
    (hch : ch.length = 57) {a r : Point} (ha : Spec.Ed448.decodePoint pk = some a)
    (hr : Spec.Ed448.decodePoint (sig.take 57) = some r) {SB : Point}
    (hSB : Rep SB (Spec.Ed448.decodeLE (sig.drop 57) • baseAff)) (b : Nat → BitVec 8)
    (hb : ∀ i (h : i < 57), b i = ch[i]) :
    Spec.Ed448.verifyEquation pk sig ch = (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
      Spec.Ed448.pointEqual (double (double (addPt SB (winQ (VG.Proof.Ed448.negPoint a) b 57))))
        (double (double r))) := by
  obtain ⟨aA, hA⟩ := decodePoint_rep ha
  obtain ⟨rA, hR⟩ := decodePoint_rep hr
  have hQ := winQ_rep hA.neg b 57
  rw [topVal_eq ch hch b hb 57 (Nat.le_refl _), Nat.sub_self, List.drop_zero] at hQ
  have h1 := double_rep (double_rep (addPt_rep hSB hQ))
  have h2 := double_rep (double_rep hR)
  have s1 := pointMul_rep 4 (pointMul_rep (Spec.Ed448.decodeLE (sig.drop 57)) basePoint_rep)
  have s2 := pointAdd_rep (pointMul_rep 4 hR) (pointMul_rep 4 (pointMul_rep (Spec.Ed448.decodeLE ch) hA))
  unfold Spec.Ed448.verifyEquation
  simp only [hpk, hsig, hch, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte, ha, hr]
  refine congrArg (decide _ && ·) (Bool.eq_iff_iff.mpr ?_)
  rw [pointEqual_rep s1 s2, pointEqual_rep h1 h2, four_iff]
  simp only [smul_neg, neg_neg]

end VG.Proof.Ed448.AArch64.Window
