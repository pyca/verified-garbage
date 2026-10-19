module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestPCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestPCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Context
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestoreCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoop
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoopCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawPrefix
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawSample
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawSampleCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadWitness
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PolicyLoopCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundBody
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResult
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundRunCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Rounds
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundsCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRoundCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MillerRabin.X86_64.Body
import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCorrect
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallStack
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerKept
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRestore
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRound
import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.MillerRabin.X86_64.CoreFrame
import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
import VerifiedGarbage.Proof.MillerRabin.X86_64.CorrectMath
import VerifiedGarbage.Proof.MillerRabin.X86_64.ExitRegisters
import VerifiedGarbage.Proof.MillerRabin.X86_64.Finish
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frames
import VerifiedGarbage.Proof.MillerRabin.X86_64.Keeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeValues
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizedPublic
import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.Primes
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.ExternalWords
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Context
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestore
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestoreCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoop
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoopCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawPrefix
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawSample
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawSampleCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadWitness
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PolicyLoopCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundBody
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResult
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundRunCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Rounds
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundsCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRoundCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Body
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallBody
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCorrect
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallStack
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerContext
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerKept
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRestore
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRound
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CoreFrame
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CorrectMath
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.ExitRegisters
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Finish
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Frames
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Keeps
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeCT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeContext
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeValues
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizedPublic
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.RsaKeyGen.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.RsaKeyGen.MrMont
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop

/-! # FFDH parameter generation on x86-64: timing of q followed by p -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.RsaKeyGen.X86_64

def CandidatePublic.afterQ (d : CandidatePublic) : CandidatePublic := { d with
  used := match d.decision true with | none => d.used | some (_, rest) => d.p.rand.length - rest.length }

private theorem status_pass {r : Option (Bool × List Byte)} (h : policyStatus r = 1) :
    ∃ rest, r = some (true, rest) := by
  cases r with
  | none => contradiction
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simp [policyStatus] at h
    · exact ⟨rest, rfl⟩

private theorem returned_next (d : CandidatePublic) (s : State)
    (h : PhaseReturned true d s ∧ isa.eval .e s = some true) : OuterState d.afterQ s := by
  have hs : policyStatus (d.decision true) = 1 := of_decide_eq_true (by
    simpa only [eval, h.1.2.2.2, Option.some.injEq] using h.2)
  obtain ⟨rest, he⟩ := status_pass hs
  obtain ⟨n, ht, hd, hr⟩ := h.1.1
  have hrest : rest = d.p.rand.drop (d.used + n) := by
    change (match d.decision true with
      | none => _ | some (pass, r) => _ ∧ r = d.p.rand.drop (d.used + n)) at hr
    rw [he] at hr
    exact hr.2
  have hcount : d.used + n = d.p.rand.length - rest.length := by
    rw [hrest, List.length_drop]
    omega_using [ht.bound]
  refine ⟨⟨?_, h.1.2.1, h.1.2.2.1⟩, hd⟩
  change CandidateTape d.p (match d.decision true with | none => d.used | some (_, r) => d.p.rand.length - r.length) s
  rw [he]
  change CandidateTape d.p (d.p.rand.length - rest.length) s
  rw [← hcount]
  exact ht

theorem PhaseLoaded.link {q : Bool} {d : CandidatePublic} {s : State} (h : PhaseLoaded q d s) :
    LinkHeader ⟨d.p.B, d.wr⟩ s := by
  obtain ⟨_, hg, hp, _⟩ := h.2
  exact ⟨h.1.2.2, hg.rdi, h.1.2.1, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact hp.link⟩

private theorem q_prime {d : CandidatePublic} {s : State}
    (h : PhaseChecked true d s ∧ isa.eval .e s = some true) : PhasePrime true d s := by
  have hs : Spec.Ffdh.primeShape (d.p.phaseValue true) = true := by
    simpa only [eval, h.1.2, Option.some.injEq] using h.2
  unfold Spec.Ffdh.primeShape at hs
  exact ⟨h.1.1, beq_iff_eq.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hs).1).2⟩

theorem testQ_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two (OuterValue false)) (testQ M.mm R.code K.run) fun _ _ => True := by
  unfold testQ
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) halveOutput_ct) halve_outer) ?_
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) (phaseSetup_ct true)) (setup_phase true)) ?_
  refine RelCT.seq (two_post (loadOutput_ct true) (load_phase true)) ?_
  refine RelCT.seq (two_post (primeCheck_ct true) (prime_checked true)) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · refine RelCT.seq (two_post
      (two_map (fun d : CandidatePublic => d) (fun _ _ h => q_prime h) (modulusPolicy_ct M R K true))
      (fun d s h => modulusPolicy_done M R K true d s (q_prime h))) ?_
    refine RelCT.seq (leaveReturned_ct true) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2.2.2, h₂.2.2.2]) ?_
      (two_taint [] (pins_nil _) (by taint_decide))
    exact two_map CandidatePublic.afterQ returned_next (testP_ct M R K)
  · exact two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic))
      (fun _ _ h => h.1.1.link) innerReject_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate
