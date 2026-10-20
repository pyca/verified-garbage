module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QBuild
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryHash
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryStack
import VerifiedGarbage.Proof.Dsa.X86.Generation.QBuildCT

/-! # A public seed and search geometry instantiate the subgroup hash timing proof -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def SeedCandidateAt (P : SearchContextPlan) (T : GenerationTape P.geometry) (used : Nat) (s : State) : Prop :=
  ∃ W, SearchContext P W s ∧ TapeMemory T s ∧ W 1 = T.pointer ∧ W 16 = BitVec.ofNat 32 used

theorem searchQBuild_ct {H : Hash} (K : HashOK H) (P : SearchContextPlan) (T : GenerationTape P.geometry)
    (used : Nat) (len : T.bytes.length = P.geometry.qLen) (final : H.F = P.geometry.qLen) :
    RelCT isa (Two fun (_ : Unit) => SeedCandidateAt P T used) (qBuild H P.geometry.qLen) (fun _ _ => True) := by
  refine two_map (fun (_ : Unit) => (⟨P.geometry.frameBase, frameUpdate P.saved 1 T.pointer⟩ : PublicFrame)) ?_
    (qBuild_ct K P.geometry.qLen)
  rintro _ s ⟨W, R, seed, source, _⟩
  have qw := P.geometry.qWidth
  have qr : q + P.geometry.qLen ≤ usedBytes P.geometry.pLen := by unfold q usedBytes domainCheck; omega
  have qs : q < usedBytes P.geometry.pLen := by omega
  have hr : VG.Impl.Dsa.Generation.Layout.hash + 8192 ≤ usedBytes P.geometry.pLen := by
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega
  have hs : VG.Impl.Dsa.Generation.Layout.hash < usedBytes P.geometry.pLen := by omega
  have sr : VG.Impl.Dsa.Generation.Layout.hash + 512 + H.S ≤ usedBytes P.geometry.pLen := by
    have := K.hSB; unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this]
  have ss : VG.Impl.Dsa.Generation.Layout.hash + 512 < usedBytes P.geometry.pLen := by
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega
  have work : VG.Impl.Dsa.Generation.Layout.hash + K.Wb ≤ usedBytes P.geometry.pLen := by
    have := K.hWb; have hw := K.hW; unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this, hw]
  have resources := hashArenaResources K R.arena (len := P.geometry.qLen) (by omega)
    (by rw [← len]; exact T.fit) (by
      apply Covers.one
      have read := seed.read 0 T.bytes.length (by omega)
      simpa only [len, off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using read)
    (by rw [← len]; exact T.part hr) (by rw [← len]; exact (T.below (Nat.le_refl _)).symm)
    (output := q) (by rw [final]; exact qr) (by
      rw [final]; exact P.geometry.parts_disjoint qr hr (.inr (by unfold q VG.Impl.Dsa.Generation.Layout.hash; decide)))
  have parent : W 5 = P.geometry.parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
  have scratch : W 14 = P.geometry.pointer VG.Impl.Dsa.Generation.Layout.hash :=
    (R.fixed 14 (by decide) (by decide)).trans P.hashPointer
  refine ⟨⟨R.arena.frame, ?_⟩, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact (R.representation 1 (by decide)).trans source
    · exact (R.representation 5 (by decide)).trans (R.fixed 5 (by decide) (by decide))
    · exact (R.representation 14 (by decide)).trans (R.fixed 14 (by decide) (by decide))
  · change HashResources K T.pointer (P.saved 5 + BitVec.ofNat 32 q) (P.saved 14) P.geometry.qLen s
    rw [P.parent, P.hashPointer]
    exact resources
end VG.Proof.Dsa.X86.Generation
