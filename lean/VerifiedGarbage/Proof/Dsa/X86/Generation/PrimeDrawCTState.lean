module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags

/-! # The next public draw and counters shared by each phase of a witness iteration -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure PrimeDrawPublic (G : PrimeConfig) where
  used : Nat
  uniform : Nat
  value : Nat
  full : used + G.draw ≤ G.tapeLen
  bound : uniform + 1 < 2 ^ 32

def drawSample (G : PrimeConfig) (p : PrimeDrawPublic G) : Nat × Bool :=
  Spec.RsaKeyGen.witness (G.modulus - 1) p.value

def drawPassed (G : PrimeConfig) (p : PrimeDrawPublic G) : Bool :=
  Spec.RsaKeyGen.mrIteration G.modulus G.twos G.exponent (drawSample G p).1

structure PrimeDrawAt (G : PrimeConfig) (p : PrimeDrawPublic G) (s : State) : Prop where
  ready : PrimeReady G s
  used : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 p.used
  count : s.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 p.uniform
  value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
    (off (G.tape.setWidth 64) (p.used + (G.draw - G.len))) G.len) = p.value

structure PrimeDrawnAt (G : PrimeConfig) (p : PrimeDrawPublic G) (s : State) : Prop where
  ready : PrimeReady G s
  pointer : s.gpr .esi = G.witness
  count : s.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 p.uniform
  value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (G.witness.setWidth 64) G.len) = p.value

structure PrimeSampledAt (G : PrimeConfig) (p : PrimeDrawPublic G) (s : State) : Prop where
  ready : PrimeReady G s
  value : wordsVal s.mem G.base (slot G.n 5) G.n = (drawSample G p).1
  flag : s.mem.readW (off G.base primeIsUniform) 32 = mask32 ((drawSample G p).2 = true)
  count : s.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 p.uniform

structure PrimeAnsweredAt (G : PrimeConfig) (p : PrimeDrawPublic G) (s : State) : Prop where
  ready : PrimeReady G s
  answer : s.gpr .eax = BitVec.ofNat 32 (drawPassed G p).toNat
  flag : s.mem.readW (off G.base primeIsUniform) 32 = mask32 ((drawSample G p).2 = true)
  count : s.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 p.uniform
end VG.Proof.Dsa.X86.Generation
