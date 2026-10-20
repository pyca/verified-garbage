module
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady

/-! # Caller resources for loading and testing a candidate from the search frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure PrimeFrameInputs (G : PrimeConfig) (frame : Addr) (words : Nat → BitVec 32) (used : Nat)
    (s : State) : Prop where
  search : SearchFrame s frame
  slots : FrameWords s.mem frame words
  base : (words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic).setWidth 64 = G.base
  write : (⟨G.base, G.size⟩ : Region) ∈ s.wr
  nowrap : G.base.toNat + G.size ≤ 2 ^ 32
  stack : StkOk (s.gpr .esp) G.base G.size
  frameScratch : Region.Disjoint ⟨frame, frameBytes⟩ ⟨G.base, G.size⟩
  frameWitness : Region.Disjoint ⟨frame, frameBytes⟩ ⟨G.witness.setWidth 64, G.len⟩
  candidateFit : (words 22).toNat + G.len ≤ 2 ^ 32
  candidateRead : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr) (off ((words 22).setWidth 64) d) 4
  candidateScratch : Region.Disjoint ⟨(words 22).setWidth 64, G.len⟩ ⟨G.base, G.size⟩
  candidate : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((words 22).setWidth 64) G.len) = G.modulus
  odd : G.modulus % 2 = 1
  gtOne : 1 < G.modulus
  tape : words 13 = G.tape
  tapeLen : words 15 = BitVec.ofNat 32 G.tapeLen
  usedValue : words 16 = BitVec.ofNat 32 used
  usedBound : used ≤ G.tapeLen
  witness : words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.witness = G.witness
  tapeRead : ∀ i < G.tapeLen, InRegions (s.rd ++ s.wr) (off (G.tape.setWidth 64) i) 1
  witnessRead : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr) (off (G.witness.setWidth 64) d) 4
  witnessReadByte : ∀ i < G.len, InRegions (s.rd ++ s.wr) (off (G.witness.setWidth 64) i) 1
  witnessWrite : ∀ i < G.len, InRegions s.wr (off (G.witness.setWidth 64) i) 1
end VG.Proof.Dsa.X86.Generation
