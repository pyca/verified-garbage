module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.Generation.Search
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributions
public import Mathlib.Tactic.Attr.Core
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryPrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparedContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext

/-! # The bounded p-search carries an accepted q and the exact remaining witness tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

structure PSearchPlan where
  context : SearchContextPlan
  seed : GenerationTape context.geometry
  seedLength : seed.bytes.length = context.geometry.qLen
  qvalue : Nat
  qPositive : 0 < qvalue
  qBound : 2 * qvalue < 2 ^ (32 * (2 * (context.geometry.pLen / 8)))
  seedUsed : BitVec 32

def PSearchPlan.value (P : PSearchPlan) (counter : Nat) : Nat :=
  Spec.Dsa.pCandidate (8 * P.context.geometry.pLen) (8 * P.context.geometry.qLen) P.qvalue P.seed.bytes
    (1 + counter * (P.context.geometry.contributionCount + 1))

def PSearchPlan.remaining (P : PSearchPlan) (counter used : Nat) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * P.context.geometry.pLen) (8 * P.context.geometry.qLen)
    P.qvalue P.seed.bytes counter (P.context.witnesses.bytes.drop used)

structure PSearchMemory (P : PSearchPlan) (W : Nat → BitVec 32) (s : State) : Prop where
  context : SearchContext P.context W s
  seed : TapeMemory P.seed s
  source : W 1 = P.seed.pointer
  qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off P.context.geometry.base q) P.context.geometry.qLen) = P.qvalue
  seedUsed : W 10 = P.seedUsed

structure PSearchAccepted (P : PSearchPlan) (value : Nat) (s : State) : Prop where
  domain : VG.Proof.Dsa.Generation.PDomain P.context.geometry.pLen value
  prepared : PrimePrepared (P.context.geometry.prime P.context.witnesses P.context.geometry.pLen value
    (by have := P.context.geometry.width; omega) (by have := P.context.geometry.width; omega)
    (by rcases P.context.geometry.width with h | h | h <;> rw [h] <;> decide) domain.bits domain.odd) s
  pBytes : Spec.Rsa.bytesAt s.mem (off P.context.geometry.base p) P.context.geometry.pLen = Spec.Dsa.encodeBE P.context.geometry.pLen value
  exponentBytes : Spec.Rsa.bytesAt s.mem (off P.context.geometry.base exponent) P.context.geometry.pLen =
    Spec.Dsa.encodeBE P.context.geometry.pLen ((value - 1) / P.qvalue)

def PSearchInvariant (P : PSearchPlan) (expected : Option (Option Nat × List Byte)) (initial : State)
    (counter : Nat) (s : State) : Prop :=
  ∃ W used, PSearchMemory P W s ∧ W 16 = BitVec.ofNat 32 used ∧ used ≤ P.context.witnesses.bytes.length ∧
    (0 < counter → W 19 = 3) ∧ expected = P.remaining counter used ∧
    Frame (parameterWrites P.context.geometry) initial.mem s.mem ∧ s.rd = initial.rd ∧ s.wr = initial.wr

def PSearchFinished (P : PSearchPlan) (expected : Option (Option Nat × List Byte)) (initial s : State) : Prop :=
  ∃ W used, PSearchMemory P W s ∧ W 16 = BitVec.ofNat 32 used ∧ used ≤ P.context.witnesses.bytes.length ∧
    ((W 19 = 0 ∧ expected = none) ∨
     (W 19 = 3 ∧ expected = some (none, P.context.witnesses.bytes.drop used)) ∨
     ∃ value, W 19 = 1 ∧ expected = some (some value, P.context.witnesses.bytes.drop used) ∧ PSearchAccepted P value s) ∧
    Frame (parameterWrites P.context.geometry) initial.mem s.mem ∧ s.rd = initial.rd ∧ s.wr = initial.wr
end VG.Proof.Dsa.X86.Generation
