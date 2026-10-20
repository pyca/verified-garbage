module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorLayout

/-! # Immutable inputs and exact remaining result of the generator search -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def generatorSearchWrites (G : PrimeConfig) (frame : Addr) (parent : BitVec 32) : List Region :=
  [⟨G.base, G.size⟩, ⟨G.witness.setWidth 64, G.len⟩, ⟨frame, frameBytes⟩,
    ⟨(generatorOutputPointer parent).setWidth 64, G.len⟩]

structure GeneratorSearchPlan where
  core : PrimeConfig
  frame : Addr
  parent : BitVec 32
  saved : Nat → BitVec 32
  tape : List Byte
  tapePtr : BitVec 32
  q : Nat
  layout : GeneratorLayout core frame parent
  base : (parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic).setWidth 64 = core.base
  savedParent : saved 5 = parent
  savedTape : saved 11 = tapePtr
  savedTotal : saved 12 = BitVec.ofNat 32 tape.length
  tapeFits : tape.length < 2 ^ 32
  tapeBounds : tapePtr.toNat + tape.length ≤ 2 ^ 32
  tapeSeparate : ∀ r ∈ generatorSearchWrites core frame parent, (⟨tapePtr.setWidth 64, tape.length⟩ : Region).Disjoint r
  exponentSeparate : ∀ r ∈ generatorSearchWrites core frame parent,
    (⟨(generatorExponentPointer parent).setWidth 64, core.len⟩ : Region).Disjoint r

def GeneratorSearchPlan.changed (P : GeneratorSearchPlan) : List Region := generatorSearchWrites P.core P.frame P.parent

def GeneratorSearchPlan.candidate (P : GeneratorSearchPlan) (used : Nat) : Nat :=
  Spec.Dsa.decodeBE ((P.tape.drop used).take P.core.len)

def GeneratorSearchPlan.value (P : GeneratorSearchPlan) (used : Nat) : Nat :=
  P.candidate used ^ ((P.core.modulus - 1) / P.q) % P.core.modulus

def GeneratorSearchPlan.accepts (P : GeneratorSearchPlan) (used : Nat) : Prop :=
  1 < P.candidate used ∧ P.candidate used < P.core.modulus - 1 ∧ 1 < P.value used

instance {P : GeneratorSearchPlan} {used : Nat} : Decidable (P.accepts used) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def GeneratorSearchPlan.remaining (P : GeneratorSearchPlan) (used : Nat) : Option Nat :=
  Spec.Dsa.generator P.core.modulus P.q
    ((Spec.Dsa.generationChunks P.core.len (P.tape.drop used)).map Spec.Dsa.decodeBE)

theorem GeneratorSearchPlan.remaining_done (P : GeneratorSearchPlan) {used : Nat}
    (h : P.tape.length - used < P.core.len) : P.remaining used = none := by
  unfold remaining
  rw [VG.Proof.Dsa.Generation.generationChunks_done (by simpa only [List.length_drop] using h)]
  rfl

theorem GeneratorSearchPlan.remaining_step (P : GeneratorSearchPlan) {used : Nat}
    (room : used + P.core.len ≤ P.tape.length) :
    P.remaining used = if P.accepts used then some (P.value used) else P.remaining (used + P.core.len) := by
  rw [remaining, VG.Proof.Dsa.Generation.generator_chunks_step (by have := P.core.lenMin; omega)
    (by simp only [List.length_drop]; omega)]
  simp only [VG.Proof.Dsa.powMod_eq, accepts, value, candidate, remaining, List.drop_drop]
  rfl
end VG.Proof.Dsa.X86.Generation
