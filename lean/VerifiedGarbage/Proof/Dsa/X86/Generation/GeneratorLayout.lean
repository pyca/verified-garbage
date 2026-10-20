module
public import Aesop.BuiltinRules
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady

/-! # Stable frame and buffer resources for testing one generator candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def generatorExponentPointer (parent : BitVec 32) : BitVec 32 :=
  parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.exponent

def generatorOutputPointer (parent : BitVec 32) : BitVec 32 :=
  parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g

structure GeneratorLayout (G : PrimeConfig) (frame : Addr) (parent : BitVec 32) : Prop where
  frameScratch : Region.Disjoint ⟨frame, frameBytes⟩ ⟨G.base, G.size⟩
  frameWitness : Region.Disjoint ⟨frame, frameBytes⟩ ⟨G.witness.setWidth 64, G.len⟩
  exponentFit : (generatorExponentPointer parent).toNat + G.len ≤ 2 ^ 32
  exponentScratch : Region.Disjoint ⟨(generatorExponentPointer parent).setWidth 64, G.len⟩ ⟨G.base, G.size⟩
  exponentWitness : Region.Disjoint ⟨(generatorExponentPointer parent).setWidth 64, G.len⟩ ⟨G.witness.setWidth 64, G.len⟩
  outputFit : (generatorOutputPointer parent).toNat + G.len ≤ 2 ^ 32
  outputScratch : Region.Disjoint ⟨(generatorOutputPointer parent).setWidth 64, G.len⟩ ⟨G.base, G.size⟩
  frameOutput : Region.Disjoint ⟨frame, frameBytes⟩ ⟨(generatorOutputPointer parent).setWidth 64, G.len⟩

structure GeneratorResources (G : PrimeConfig) (frame : Addr) (parent : BitVec 32)
    (words : Nat → BitVec 32) (s : State) : Prop where
  ready : PrimeReady G s
  searchFrame : SearchFrame s frame
  representation : FrameWords s.mem frame words
  savedParent : words 5 = parent
  exponentRead : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr)
    (off ((generatorExponentPointer parent).setWidth 64) d) 4
  outputWrite : ∀ e k, e + k ≤ G.len → InRegions s.wr
    (off ((generatorOutputPointer parent).setWidth 64) e) k

theorem GeneratorLayout.frameApart {G : PrimeConfig} {frame : Addr} {parent : BitVec 32}
    (L : GeneratorLayout G frame parent) : ∀ r ∈ [⟨G.base, G.size⟩, ⟨G.witness.setWidth 64, G.len⟩],
      (⟨frame, frameBytes⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact L.frameScratch
  · exact L.frameWitness

theorem GeneratorLayout.exponentApart {G : PrimeConfig} {frame : Addr} {parent : BitVec 32}
    (L : GeneratorLayout G frame parent) : ∀ r ∈ [⟨G.base, G.size⟩, ⟨G.witness.setWidth 64, G.len⟩],
      (⟨(generatorExponentPointer parent).setWidth 64, G.len⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact L.exponentScratch
  · exact L.exponentWitness
end VG.Proof.Dsa.X86.Generation
