module
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Round
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Spills

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Box
import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundFunction
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE

def contribution (r k : BitVec 64) (i : Nat) : BitVec 64 :=
  (boxPiece i (Spec.TripleDes.sBox i
    (roundChunk i (r.setWidth 32) (k.setWidth 48)))).zeroExtend 64

/-- Compose any ordered list of S-boxes. The schedule word and Feistel
right half stay fixed; each contribution is XORed into the left half. -/
theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r k : BitVec 64) (s : State) (hok : Ok sboxCfg s)
    (hr : s.gpr .r15 = r) (hk : s.mem.readW (s.gpr .r17) 64 = k)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r17) 8)
    (hsep : (⟨s.gpr .r17, 8⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .r14 = indices.foldl (fun out i => out ^^^ contribution r k i) (s.gpr .r14) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ roundKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil =>
    exact ⟨s, runBlock_nil, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    have hi : i < 8 := hindices i (List.mem_cons_self)
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, keep₁, frame₁⟩ := box_ok i hi s hok hread
    have hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, keep₁ .r5 (by decide)]
    have hr₁ : s₁.gpr .r15 = r := (keep₁ .r15 (by decide)).trans hr
    have hk₁ : s₁.mem.readW (s₁.gpr .r17) 64 = k := by
      rw [keep₁ .r17 (by decide)]
      refine Eq.trans (frame₁.readW (r := ⟨s.gpr .r17, 8⟩) ?_ ?_ (by decide)) hk
      · simp [Region.Contains]
      · intro q hq
        obtain rfl := List.mem_singleton.mp hq
        exact hsep
    have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r17) 8 := by
      rw [rd₁, wr₁, keep₁ .r17 (by decide)]
      exact hread
    have hsep₁ : (⟨s₁.gpr .r17, 8⟩ : Region).Disjoint (spillRegion s₁) := by
      rw [keep₁ .r17 (by decide), hregion]
      exact hsep
    have hok₁ : Ok sboxCfg s₁ := hok.congr
      (keep₁ .r5 (by decide)) (keep₁ .r5 (by decide)) rd₁ wr₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ hok₁ hr₁ hk₁ hread₁ hsep₁
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
    · simp only [List.flatMap_cons, runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .r14 = s.gpr .r14 ^^^ contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · exact fun q hq => (keep₂ q hq).trans (keep₁ q hq)
    · rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r k : BitVec 64) (l : BitVec 64) :
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) l =
      l ^^^ (Spec.TripleDes.roundFunction (r.setWidth 32) (k.setWidth 48)).zeroExtend 64 := by
  rw [foldl_xor_start]
  have hf := foldl_xor_extend (List.range 8)
    (fun i => boxPiece i (Spec.TripleDes.sBox i
      (roundChunk i (r.setWidth 32) (k.setWidth 48)))) 0
  have hz : (0 : BitVec 32).setWidth 64 = 0 := BitVec.setWidth_zero 64 32
  have hinit := congrArg (fun b : BitVec 64 =>
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) b) hz
  have hg := congrArg (BitVec.setWidth 64)
    (boxPieces_eq_roundFunction (r.setWidth 32) (k.setWidth 48))
  exact congrArg (fun x => l ^^^ x) ((hinit.symm.trans hf).trans hg)

/-- The registers the half swap keeps. -/
def roundOuterKept : List Reg := [.r2, .r3, .r4, .r5, .r16, .r17, .r18, .r19, .r29, .r30, .r31]

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .r14 = s.gpr .r15 ∧ s'.gpr .r15 = s.gpr .r14 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  let s₁ := s.write .r6 (s.gpr .r14 ||| s.gpr .r14)
  let s₂ := s₁.write .r14 (s₁.gpr .r15 ||| s₁.gpr .r15)
  let s₃ := s₂.write .r15 (s₂.gpr .r6 ||| s₂.gpr .r6)
  refine ⟨s₃, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [swapHalves, rr, rr, rr, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, gpr_write, BitVec.or_self, reduceCtorEq, ite_true, ite_false]
  · simp only [s₃, s₂, s₁, gpr_write, BitVec.or_self, reduceCtorEq, ite_true, ite_false]
  · intro q hq
    have hne : q ≠ .r6 ∧ q ≠ .r14 ∧ q ≠ .r15 := by revert hq; cases q <;> decide
    simp only [s₃, s₂, s₁, gpr_write, hne.1, hne.2.1, hne.2.2, ite_false]

/-- One full Feistel round, with all eight S-boxes and the half swap. -/
theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .r17) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r17) 8)
    (hsep : (⟨s.gpr .r17, 8⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .r14 = r.setWidth 64 ∧
      s'.gpr .r15 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, keep₁, frame₁⟩ := boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) (r.setWidth 64) k s hok hr hk hread hsep
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, mem₂, keep₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .r15 (by decide)).trans hr)
  · rw [right, value, contributions_roundFunction, hl]
    have hwidth : (r.setWidth 64).setWidth 32 = r := by simp
    rw [hwidth]
    exact BitVec.setWidth_xor.symm
  · intro q hq
    have hq' : q ∈ roundKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')
  · rw [mem₂]
    exact frame₁

end VG.Proof.TripleDes.PPC64LE
