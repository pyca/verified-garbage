module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombTbl
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The comb's tables

The comb's tables at `T` (`TblAt`): readable, beyond the working space, word
`i` the static's `combWord i` (`combWord_eq`), the cached form of table `j`'s
entry `m + 1`'s coordinate. Nothing here unfolds a table: each lemma holds for
any words.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 VG.Proof.X25519
open Word64

/-! ## The tables -/

/-- The comb's tables at `T`: readable, beyond the working space at `base`, word `i` the
static's (`combWord i`). -/
structure TblAt (s : State) (base T : Addr) : Prop where
  rd : InRegions (s.rd ++ s.wr) T (8 * (64 * 96))
  far : ∀ i < 8 * (64 * 96), 8192 ≤ ofs base (T + BitVec.ofNat 64 i)
  val : ∀ i < 64 * 96, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = combWord i

theorem tbl_add (T : Addr) (a b : Nat) :
    T + BitVec.ofNat 64 a + BitVec.ofNat 64 b = T + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The tables survive what keeps the regions and the memory beyond the working space. -/
theorem TblAt.of_far {s t : State} {base T : Addr} (h : TblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : ∀ x, 8192 ≤ ofs base x → t.mem x = s.mem x) :
    TblAt t base T :=
  ⟨hrw ▸ h.rd, h.far, fun i hi => by
    rw [← h.val i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [tbl_add T _ _]
    exact h.far _ (by omega)⟩

/-- The tables, from a contract's facts: readable, and apart from the working space at `base`,
one of the regions `wr`. -/
theorem CombHeld.tblAt {s : State} {wr : List Region} {base : Addr} (h : CombHeld s wr)
    (hrd : (⟨s.syms combSym, 8 * combWords.length⟩ : Region) ∈ s.rd ++ s.wr)
    (hsc : (⟨base, 8192⟩ : Region) ∈ wr) : TblAt s base (s.syms combSym) := by
  obtain ⟨held, fit, dj⟩ := h
  rw [combWords_length] at held fit dj hrd
  have hc : Region.Contains ⟨s.syms combSym, 8 * (64 * 96)⟩ (s.syms combSym) (8 * (64 * 96)) := by
    have := Offset.contains_base (s.syms combSym) (d := 0) (n := 8 * (64 * 96)) (k := 8 * (64 * 96))
      (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine ⟨⟨_, hrd, hc⟩, fun i hi => ?_, fun i hi => ?_⟩
  · refine Nat.le_of_not_lt fun hlt => dj _ hsc _
      (Offset.contains_base _ (d := i) (n := 1) (k := 8 * (64 * 96)) (by omega) (by omega)) ?_
    simp only [Region.Contains]; simp only [ofs] at hlt; omega
  · rw [← combWords_getD hi, ← held i hi]

theorem feWord_val (v : Spec.X25519.Fe) :
    val4 (feWord v 0) (feWord v 1) (feWord v 2) (feWord v 3) = v.val := by
  simp only [feWord, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

/-- The cached point in slots `a`, `b`, `c`. -/
def cachedAt (e : Env) (a b c : Slot) : Spec.Ed25519.Point := ⟨e a, e b, e c, 2⟩

/-- Coordinate `c` of a cached point in the tables: `Y - X`, `Y + X`, `2dT`. -/
def coord : Nat → Spec.Ed25519.Point → Spec.X25519.Fe
  | 0, p => p.X
  | 1, p => p.Y
  | _, p => p.Z

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  unfold combCached
  split
  · rfl
  · split; rfl

theorem combCached64_zero (j : Nat) : combCached64 j 0 = ⟨1, 1, 0, 2⟩ := by
  unfold combCached64; split <;> rfl

theorem combCached64_T (j a : Nat) : (combCached64 j a).T = 2 := by
  unfold combCached64
  split
  · exact combCached_T _ _
  · unfold combCached16
    split
    · rfl
    · split; rfl

theorem cachedAt_eq {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point} (hq : q.T = 2)
    (ha : e a = q.X) (hb : e b = q.Y) (hc : e c = q.Z) : cachedAt e a b c = q := by
  cases q
  simp only [cachedAt, ha, hb, hc] at hq ⊢
  rw [hq]

/-! ## The tables' words -/

/-- Word `96 j + 32 c + 4 m + w` of the tables is word `w` of coordinate `c` of entry `m + 1` of
table `j`. -/
theorem combWord_eq {j c m w : Nat} (hc : c < 3) (hm : m < 8) (hw : w < 4) :
    combWord (96 * j + 32 * c + 4 * m + w) = feWord (coord c (combCached64 j (m + 1))) w := by
  have e1 : (96 * j + 32 * c + 4 * m + w) / 96 = j := by omega
  have e2 : (96 * j + 32 * c + 4 * m + w) % 32 / 4 + 1 = m + 1 := by omega
  have e3 : (96 * j + 32 * c + 4 * m + w) % 4 = w := by omega
  have e4 : (96 * j + 32 * c + 4 * m + w) % 96 = 32 * c + 4 * m + w := by omega
  unfold combWord
  simp only [e1, e2, e3, e4]
  refine congrArg (feWord · w) ?_
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · simp only [show 32 * 0 + 4 * m + w < 32 from by omega, ite_true]; rfl
  · simp only [show ¬ 32 * 1 + 4 * m + w < 32 from by omega, show 32 * 1 + 4 * m + w < 64 from by omega,
      ite_true, ite_false]; rfl
  · simp only [show ¬ 32 * 2 + 4 * m + w < 32 from by omega, show ¬ 32 * 2 + 4 * m + w < 64 from by omega,
      ite_false]; rfl

end VG.Proof.Ed25519.AArch64
