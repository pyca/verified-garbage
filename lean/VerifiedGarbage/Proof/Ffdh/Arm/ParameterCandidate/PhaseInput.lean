module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontPrepare

/-! Phase arguments after the native q/p policy header has been initialized. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

structure PhaseInput (p : WitnessParams) (src : BitVec 32) (k used : Nat) (s : State) : Prop where
  preparation : MontPrepInput p.base src p.capacity k s
  saved : SavedFrame (witnessValues p used 0) witnessSlots s
  words : p.words = Spec.Rsa.modulusWords k
  modulus : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) = p.modulus
  space : Spec.Rsa.scratchWords k ≤ p.capacity
  stackScratch : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  stackBelow : 56 ≤ s.sp.toNat
  belowScratch : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  bitsExact : p.bits = Spec.RsaKeyGen.bitLength (p.modulus - 1)
  bitsPositive : 0 < p.bits
  bitsBound : p.bits ≤ 8192
  bitsFit : p.bits ≤ 64 * p.words
  checksPositive : 0 < p.checks
  checksBound : p.checks ≤ 128
  usedBound : used ≤ p.bytes.length
  tapeCount : p.bytes.length < 2 ^ 32
  tapeFits : p.tape.toNat + p.bytes.length ≤ 2 ^ 32
  tapeRead : InRegions (s.rd ++ s.wr) (State.addr p.tape) p.bytes.length
  tapeScratch : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  tapeStack : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint ⟨State.addr s.sp, 72⟩
  tapeBelow : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint (FrameStack.belowA s.sp 56)
  tapeBytes : Spec.Rsa.bytesAt s.mem (State.addr p.tape) p.bytes.length = p.bytes

end VG.Proof.Ffdh.Arm.ParameterCandidate
