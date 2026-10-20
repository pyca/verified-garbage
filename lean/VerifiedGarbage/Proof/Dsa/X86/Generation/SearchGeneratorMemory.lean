module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryGeneratorPlan
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchMemory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # An accepted p and its saved quotient supply the generator-search resources -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def PSearchAccepted.core {P : PSearchPlan} {value : Nat} {s : State} (A : PSearchAccepted P value s) : PrimeConfig :=
  P.context.geometry.prime P.context.witnesses P.context.geometry.pLen value
    (by have := P.context.geometry.width; omega) (by have := P.context.geometry.width; omega)
    (by rcases P.context.geometry.width with h | h | h <;> rw [h] <;> decide) A.domain.bits A.domain.odd

def searchGeneratorPlan {P : PSearchPlan} {value : Nat} {W : Nat → BitVec 32} {s : State}
    (R : PSearchMemory P W s) (A : PSearchAccepted P value s) : GeneratorSearchPlan :=
  P.context.geometry.generatorPlan A.core P.context.hs W P.qvalue rfl rfl rfl
    ((R.context.fixed 5 (by decide) (by decide)).trans P.context.parent)
    ((R.context.fixed 11 (by decide) (by decide)).trans P.context.hPointer)
    ((R.context.fixed 12 (by decide) (by decide)).trans P.context.hLength)

theorem searchGeneratorMemory {P : PSearchPlan} {value : Nat} {W : Nat → BitVec 32} {s : State}
    (R : PSearchMemory P W s) (A : PSearchAccepted P value s) : GeneratorSearchMemory (searchGeneratorPlan R A) W s := by
  have pw := P.context.geometry.width
  have er : exponent + P.context.geometry.pLen ≤ usedBytes P.context.geometry.pLen := by unfold exponent usedBytes domainCheck; omega
  have gr : g + P.context.geometry.pLen ≤ usedBytes P.context.geometry.pLen := by unfold g usedBytes domainCheck; omega
  have es : exponent < usedBytes P.context.geometry.pLen := by omega
  have gs : g < usedBytes P.context.geometry.pLen := by omega
  have bound : (value - 1) / P.qvalue < 256 ^ P.context.geometry.pLen := by
    have upper := A.domain.upper
    rw [Nat.pow_mul] at upper
    change value < 256 ^ P.context.geometry.pLen at upper
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  refine ⟨A.prepared, R.context.arena.frame, R.context.representation, fun _ _ _ => rfl,
    R.context.hs.value, ?_, R.context.hs.read, ?_, ?_⟩
  · change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((generatorExponentPointer P.context.geometry.parent).setWidth 64)
      P.context.geometry.pLen) = _
    rw [show (generatorExponentPointer P.context.geometry.parent).setWidth 64 = off P.context.geometry.base exponent
      from P.context.geometry.pointer_addr es, A.exponentBytes, VG.Proof.Dsa.decodeBE_encodeBE bound]
    rfl
  · intro d hd
    exact R.context.arena.readPointer es er d 4 hd
  · intro d k hk
    exact R.context.arena.writePointer gs gr d k hk
end VG.Proof.Dsa.X86.Generation
