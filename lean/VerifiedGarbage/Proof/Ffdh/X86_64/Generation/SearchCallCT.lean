module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.AbiCorrect
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallLayout
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
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.CandidatePre
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.OutgoingPre
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Body
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.BodyCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CandidateCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestoreCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoop
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoopCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawPrefix
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawSample
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawSampleCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.EntryCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.GeneratorCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.InitialStages
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadWitness
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PolicyLoopCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ResultBridge
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundBody
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResult
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundRunCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Rounds
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundsCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestP
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestPCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestQ
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestQCT
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
import VerifiedGarbage.Spec.Ffdh.GenerationContract
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Internal candidate calls retain the existing public-tape timing contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_arguments_ready (p : SearchPoint) (s : State) (h : SearchAllocated p s) :
    WP isa (.block arguments) s (SearchCallCT p) := by
  obtain ⟨original, before, h, rfl⟩ := h
  refine WP.mono (search_arguments_ok h) fun t ⟨ha, hm, k⟩ => ?_
  have hsp : t.gpr .rsp = before.gpr .rsp - 32 := k.gpr (by decide)
  have hw := search_call_writes h k.2.2
  exact ⟨⟨search_call_pre h ha hm k, (search_call_reads h k.2.1 k.2.2).append_left hw.right, hw⟩,
    ha, by rw [hsp, h.rsp], search_call_random h ha hm hsp,
    search_call_args hsp hm 0 (by decide), search_call_args hsp hm 1 (by decide),
    search_call_args hsp hm 2 (by decide)⟩

private theorem call_pub {p : SearchPoint} {s t : State} (h₁ : SearchCallCT p s) (h₂ : SearchCallCT p t) :
    pcPub (s.withRegions (callReads p.inputs p.used) (callWrites p.inputs))
      (t.withRegions (callReads p.inputs p.used) (callWrites p.inputs)) := by
  obtain ⟨_, ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩, sp₁, rand₁, n₁, scr₁, len₁⟩ := h₁
  obtain ⟨_, ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩, sp₂, rand₂, n₂, scr₂, len₂⟩ := h₂
  exact ⟨sp₁.trans sp₂.symm, by change (pcRand s).map (·.toNat) = (pcRand t).map (·.toNat); rw [rand₁, rand₂],
    a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm, d₁.trans d₂.symm,
    congrArg (BitVec.setWidth 32) (e₁.trans e₂.symm), f₁.trans f₂.symm,
    n₁.trans n₂.symm, scr₁.trans scr₂.symm, len₁.trans len₂.symm⟩

theorem search_candidate_inline_ct (v : RoundImpl) :
    RelCT isa (Two SearchCallCT) (candidateCode v) (fun _ _ => True) := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ ⟨p, h₁, h₂⟩ he₁ he₂
  have hc := pc_correct v.mont (R2Impl.words v.mont) (Kernel.called v)
    (SpSafe.of_all (candidateCode_sp v)) (candidateCode_depth v) (candidateCode_mx v)
  have ct := inline_constantTime (k := pcContract)
    (fun s h => by obtain ⟨tr, t, he, _, _⟩ := hc s h; exact ⟨tr, t, he⟩)
    (pc_constantTime v.mont (R2Impl.words v.mont) (Kernel.called v))
    (fun _ => callReads p.inputs p.used) (fun _ => callWrites p.inputs)
  exact ⟨ct _ _ _ _ _ _ h₁.1 h₂.1 (call_pub h₁ h₂) he₁ he₂, trivial⟩

theorem search_candidate_run_ct (v : RoundImpl) :
    RelCT isa (Two SearchCTL) (candidateRun (candidateCode v)) (fun _ _ => True) := by
  unfold candidateRun
  apply frame_alloc_ct
  refine (RelCT.seq (two_piece [.r12, .rsp] search_allocated_pins (by taint_decide)
    search_arguments_ready) (search_candidate_inline_ct v)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨p, ⟨o₁, h₁⟩, ⟨o₂, h₂⟩⟩, rfl, rfl⟩
  exact ⟨p, ⟨o₁, s, h₁, rfl⟩, ⟨o₂, t, h₂, rfl⟩⟩

end VG.Proof.Ffdh.X86_64.Generation
