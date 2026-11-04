module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.CT
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.CT

/-!
# Deterministic ECDSA on PPC64LE: the curve

What the proof needs of the curve (`RfcCurve`), which each curve's file
builds: the signature with a given `k` (`Core`), and, for the sizes of each
index's hash function (`hidx`, `cfgS`), the facts the proof of the code needs
(`SizeOk`) and the taint checks of the blocks that depend on the scalars'
sizes (`CBlks`); those that depend only on the hash function's (`HBlks`) are
decided here. It imports none of the hash functions' proofs, so that the
curves' files, whose checks build in parallel, do not either.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE

/-! ## The sizes -/

/-- What the proof needs of the sizes of the curve `E`, of `k` 32-bit words
unless `wide`, and a hash function's. -/
structure SizeOk (E : Spec.Ecdsa.Instance) (k : Nat) (c : Cfg) : Prop where
  hk : c.wide = false → c.len = 4 * k
  hk16 : c.wide = false → k ≤ 16
  hbits : c.wide = false → Spec.Ecdsa.nBits E.curve = 8 * c.len
  hn₁ : c.wide = false → c.n < 2 ^ (32 * k)
  hn₂ : c.wide = false → 2 ^ (32 * k) < 2 * c.n
  hW : c.wide = true → c.len ≤ 66 ∧ Spec.Ecdsa.nBits E.curve = 8 * c.len - c.sh ∧ c.sh < 8 ∧
    (c.sh ≠ 0 → c.len = 66) ∧ c.len ≤ c.m * c.D ∧ c.m * c.D ≤ 128 ∧ E.curve.n ≠ 0

/-- The indices of the hash functions with HMAC that have tables on PPC64LE:
all of `idxs` but MD5's. -/
def hidx : List Nat := [1, 2, 3, 4, 5, 6, 7]

theorem hidx_sub {i : Nat} (h : i ∈ hidx) : i ∈ idxs := by
  simp only [hidx, idxs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega

/-- The code's sizes for the scalars of `E` and index `i`'s hash function. -/
def cfgS (E : Spec.Ecdsa.Instance) (i : Nat) : Cfg :=
  ⟨(shapeOf i).1, (shapeOf i).2, ⟨[], [], []⟩, E.curve.len, E.curve.n, 1, "", .block []⟩

/-- The code's sizes for index `i`'s hash function. -/
def cfgH (i : Nat) : Cfg := ⟨(shapeOf i).1, (shapeOf i).2, ⟨[], [], []⟩, 0, 0, 1, "", .block []⟩

theorem SizeOk.of {E : Spec.Ecdsa.Instance} {k : Nat} {c c' : Cfg} (h : SizeOk E k c') (hD : c.D = c'.D)
    (hl : c.len = c'.len) (hn : c.n = c'.n) : SizeOk E k c := by
  obtain ⟨D, B, f, len, n, t, cn, cc⟩ := c
  obtain ⟨D', B', f', len', n', t', cn', cc'⟩ := c'
  simp only at hD hl hn; subst hD hl hn
  exact ⟨h.hk, h.hk16, h.hbits, h.hn₁, h.hn₂, h.hW⟩

theorem HBlks.of {c c' : Cfg} (h : HBlks c') (hD : c.D = c'.D) (hB : c.B = c'.B) : HBlks c := by
  obtain ⟨D, B, f, len, n, t, cn, cc⟩ := c
  obtain ⟨D', B', f', len', n', t', cn', cc'⟩ := c'
  simp only at hD hB; subst hD hB
  exact ⟨h.pad, h.outK, h.outV, h.keep⟩

theorem CBlks.of {c c' : Cfg} (h : CBlks c') (hD : c.D = c'.D) (hl : c.len = c'.len) (hn : c.n = c'.n) :
    CBlks c := by
  obtain ⟨D, B, f, len, n, t, cn, cc⟩ := c
  obtain ⟨D', B', f', len', n', t', cn', cc'⟩ := c'
  simp only at hD hl hn; subst hD hl hn
  exact ⟨h.msgF, h.msgN, h.red, h.hPrep, h.xPrep, h.conv₁, h.conv₂⟩

/-- The keeping of `V`'s `D` bytes to the candidate, for `D` of 20 bytes or more. -/
theorem keep_of {c : Cfg} (h20 : 20 ≤ c.D) (h : ∀ j < 6, j * c.D + c.D ≤ 128 → TaintOk [] (c.keepV j)) :
    ∀ j, j * c.D + c.D ≤ 128 → TaintOk [] (c.keepV j) := fun j hj => by
  have : j < 6 := by
    rcases Nat.lt_or_ge j 6 with h' | h'
    · exact h'
    · have := Nat.mul_le_mul_right c.D h'; omega
  exact h j this hj

/-- Index `i`'s blocks that depend only on its hash function's sizes. -/
theorem hblk₁ : HBlks (cfgH 1) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, keep_of (by decide) fun j hj _ => by
    obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    all_goals exact ⟨_, by taint_decide⟩⟩
theorem hblk₂ : HBlks (cfgH 2) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, keep_of (by decide) fun j hj hk => by
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
      simp only [cfgH, shapeOf] at hk; omega
    all_goals exact ⟨_, by taint_decide⟩⟩
theorem hblk₃ : HBlks (cfgH 3) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, keep_of (by decide) fun j hj hk => by
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
      simp only [cfgH, shapeOf] at hk; omega
    all_goals exact ⟨_, by taint_decide⟩⟩
theorem hblk₄ : HBlks (cfgH 4) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, keep_of (by decide) fun j hj hk => by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by simp only [cfgH, shapeOf] at hk; omega
    all_goals exact ⟨_, by taint_decide⟩⟩
theorem hblk₅ : HBlks (cfgH 5) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, keep_of (by decide) fun j hj hk => by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by simp only [cfgH, shapeOf] at hk; omega
    all_goals exact ⟨_, by taint_decide⟩⟩
theorem hblk₆ : HBlks (cfgH 6) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, keep_of (by decide) fun j hj hk => by
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
      simp only [cfgH, shapeOf] at hk; omega
    all_goals exact ⟨_, by taint_decide⟩⟩
theorem hblk₇ : HBlks (cfgH 7) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, keep_of (by decide) fun j hj hk => by
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
      simp only [cfgH, shapeOf] at hk; omega
    all_goals exact ⟨_, by taint_decide⟩⟩

theorem hblk : ∀ i ∈ hidx, HBlks (cfgH i) := by
  intro i hi
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hblk₁, hblk₂, hblk₃, hblk₄, hblk₅, hblk₆, hblk₇]

/-! ## The curve and the code -/

/-- What the proof needs of a curve, which its file shows: the signature with
a given `k`, of `k` 32-bit words unless `wide`, the facts of the sizes of
each index's code, and the taint checks of the blocks that depend on the
scalars' sizes. -/
structure RfcCurve where
  R : Core
  k : Nat
  sizes : ∀ i ∈ hidx, SizeOk R.E k (cfgS R.E i)
  cblk : ∀ i ∈ hidx, CBlks (cfgS R.E i)

/-! ## What each curve's file decides -/

/-- Decides `SizeOk` of a curve's sizes for one index. -/
macro "size_ok" : tactic => `(tactic| exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
  by decide +kernel, by decide +kernel, by decide +kernel⟩)

/-- Decides `CBlks` of a curve's sizes for one index: the taint checks of the
blocks the sizes have, the others absurd. -/
macro "cblk_ok" : tactic => `(tactic| (refine ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, fun h => ?_, fun h => ?_,
  fun h hs => ?_, fun h hs => ?_, fun h hs => ?_⟩ <;>
  first | exact absurd h (by decide) | exact absurd hs (by decide +kernel) | exact ⟨_, by taint_decide⟩))

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
