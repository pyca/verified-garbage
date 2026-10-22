module

import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTimingLoop
public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinInit
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessChecksTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTimingState

/-! # The complete prepared primality loop reveals only its consumed entropy length -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

def Parameters.iterations (P : Parameters) : Nat :=
  itersOf P.bytes P.entropy.length (shapeOf P.test) P.start - 1

def Initial (P : Parameters) (s : State) : Prop :=
  Prepare.Data P.g P.candidate P.capacity P.p s ∧
    InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen ∧
    Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy ∧
    s.mem.readW (off P.g.W 28) 32 = P.rand ∧ w32 s.mem P.g.W 32 = P.randLen ∧
    w32 s.mem P.g.W 152 = P.start

def InitialPair (P : Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (s t : State) : Prop :=
  Pair P.g [.edi] s t ∧ Initial P s ∧ Initial (P.withSecret other entropy) t ∧
    P.iterations = (P.withSecret other entropy).iterations

theorem init_pair {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.codeOf P.checks))
      (LoopPair P other entropy 0 P.iterations) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := WitnessChecks.codeOf_trace P.checks _ _ _ _ _ _ H.1.2.2 E G
  obtain ⟨S, readS, bytesS, ptrS, lenS, usedS⟩ := H.2.1
  obtain ⟨T, readT, bytesT, ptrT, lenT, usedT⟩ := H.2.2.1
  obtain ⟨U, _, _, _⟩ := wp_result (init_ok v S readS bytesS ptrS lenS usedS enough) E
  obtain ⟨Z, _, _, _⟩ := wp_result (init_ok w T readT bytesT ptrT lenT usedT enough) G
  have iters := H.2.2.2
  change P.iterations = (P.withSecret other entropy).iterations at iters
  change StateAt (P.withSecret other entropy) 0 (P.withSecret other entropy).iterations z at Z
  rw [← iters] at Z
  exact ⟨trace, ⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩, U, Z⟩

theorem code_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (codeOf P.checks P.g.w montName mont roundName round) (Pair P.g [.edi]) := by
  unfold codeOf
  exact RelCT.seq (init_pair v w enough)
    (loop_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v w 0 P.iterations)

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
