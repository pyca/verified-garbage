module
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorLayout
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public import VerifiedGarbage.Spec.Rsa.Contract
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorPowerCT

/-! # Public data controlling a generator candidate's trace -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure GeneratorCandidatePublic where
  frame : PublicFrame
  input : BitVec 32
  value : Nat
  exponent : Nat

def GeneratorCandidatePublic.power (G : PrimeConfig) (p : GeneratorCandidatePublic) : GeneratorPublic :=
  ⟨G.base, G.size, G.modulus, p.value, p.exponent⟩

def GeneratorFrameAt (G : PrimeConfig) (p : GeneratorCandidatePublic) (s : State) : Prop :=
  ∃ W, GeneratorResources G p.frame.base (p.frame.words 5) W s

structure GeneratorCandidateAt (G : PrimeConfig) (p : GeneratorCandidatePublic) (s : State) : Prop where
  layout : GeneratorLayout G p.frame.base (p.frame.words 5)
  resources : GeneratorFrameAt G p s
  pointer : s.gpr .esi = p.input
  value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.input.setWidth 64) G.len) = p.value
  exponent : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
    ((generatorExponentPointer (p.frame.words 5)).setWidth 64) G.len) = p.exponent
  fit : p.input.toNat + G.len ≤ 2 ^ 32
  read : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr) (off (p.input.setWidth 64) d) 4
  apart : Region.Disjoint ⟨p.input.setWidth 64, G.len⟩ ⟨G.base, G.size⟩

structure GeneratorRangeAt (G : PrimeConfig) (p : GeneratorCandidatePublic) (s : State) : Prop where
  layout : GeneratorLayout G p.frame.base (p.frame.words 5)
  resources : GeneratorFrameAt G p s
  value : wordsVal s.mem G.base (slot G.n 5) G.n = p.value
  exponent : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
    ((generatorExponentPointer (p.frame.words 5)).setWidth 64) G.len) = p.exponent
  zero : s.zf = some (decide (¬ (1 < p.value ∧ p.value < G.modulus - 1)))
end VG.Proof.Dsa.X86.Generation
