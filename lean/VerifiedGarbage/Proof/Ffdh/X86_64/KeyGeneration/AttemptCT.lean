module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptRun
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptStep
meta import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CallEntry
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
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
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Inline
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.OutgoingPre
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchAccept
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchAcceptDone
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallLayout
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClear
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDoneUpdate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntry
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchExhausted
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRejectHeaders
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRejectStep
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRequest
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRequestDone
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchUpdate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Exits
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Guards
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Loop
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Rejects
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoop
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawPrefix
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawSample
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadWitness
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundBody
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResult
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Rounds
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
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
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
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
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Spec.Ffdh.GenerationContract
import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
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

/-! # An attempt leaks only the domain and its status

The attempt's timing may depend on the domain and its status
(`attemptContract.pub`). Two runs at the same point agree on both: the
status is the first of the statuses still to come.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.X86_64.Generation (writeController allocated allocated_rsp frame_alloc_ct)
open VG.Proof.Ffdh.X86_64.GenerateKey (gkLeak gkDom gkRand gkA gkS)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- A loop state at which the controller attempts a key. -/
def KeyReady (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated 40 s

/-- The attempt's entry, before the call. -/
def KeyCallCT (q : KeyPoint) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    KeyArgs q.inputs u ∧
    u.mem = writeController s.mem (s.gpr .rsp - 40) (callValues q.inputs q.used) ∧
    Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 40 s) u

/-- After the attempt. -/
def KeyAttempted (q : KeyPoint) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs (keyRand original) q.used t

theorem key_allocated_pins : Pins KeyAllocated [.r12, .rsp] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h₁.r12.trans h₂.r12.symm
  · rw [allocated_rsp, allocated_rsp, h₁.rsp, h₂.rsp]

private theorem arguments_ready (q : KeyPoint) (u : State) (h : KeyAllocated q u) :
    WP isa (.block arguments) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, h, hst⟩, hk, hs, hr⟩, rfl⟩ := h
  exact WP.mono (key_arguments_ok h) fun _ ⟨ha, hm, k⟩ => ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩

theorem key_attempt_ready (v : RoundImpl) (q : KeyPoint) (s : State) (h : KeyReady q s) :
    WP isa (attemptRun (attemptCall v)) s (KeyAttempted q) := by
  obtain ⟨⟨original, h, hst⟩, hk, hs, hr⟩ := h
  exact WP.mono (key_attempt_run v h hr) fun _ ⟨ht, hp⟩ => ⟨original, ht, hst, hk, hs, hr, hp⟩

/-- What the attempt sees at its entry, in terms of the point alone. -/
private theorem call_view {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    (callState q.inputs q.used u).gpr .rsp = q.inputs.sp - 40 - 8 ∧
    gkLeak (callState q.inputs q.used u) = q.inputs.dom.map (·.toNat) ++ q.statuses.head?.toList ∧
    (callState q.inputs q.used u).gpr .rdi = q.inputs.xp ∧
    (callState q.inputs q.used u).gpr .rsi = BitVec.ofNat 64 q.inputs.len ∧
    (callState q.inputs q.used u).gpr .rdx = q.inputs.yp ∧
    (callState q.inputs q.used u).gpr .rcx = BitVec.ofNat 64 q.inputs.len ∧
    (callState q.inputs q.used u).gpr .r8 = q.inputs.dp ∧
    (callState q.inputs q.used u).gpr .r9 = BitVec.ofNat 64 q.inputs.dlen ∧
    stackArg (callState q.inputs q.used u) 0 = BitVec.ofNat 64 q.inputs.len ∧
    stackArg (callState q.inputs q.used u) 1 = q.inputs.rp + BitVec.ofNat 64 q.used ∧
    stackArg (callState q.inputs q.used u) 2 = BitVec.ofNat 64 q.inputs.len ∧
    stackArg (callState q.inputs q.used u) 3 = q.inputs.B ∧
    stackArg (callState q.inputs q.used u) 4 = BitVec.ofNat 64 (q.inputs.Z / 8) := by
  obtain ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩ := h
  have hu : u.gpr .rsp = q.inputs.sp - 40 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp]; rfl
  have hf := h.callFacts hr
  obtain ⟨hdom, hrand, hlen⟩ := call_inputs h hr hf hm hu ha
  have hlen' : (keyRand original).length = q.inputs.randLen := by
    rw [← h.random]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have hhead := keyTail_statuses_head (a := q.inputs.a) (len := q.inputs.len) (rand := keyRand original) (used := q.used)
    hk hs (by rw [hlen']; omega)
  rw [hst] at hhead
  obtain ⟨h0, h1, h2, h3, h4⟩ := call_args hu h.rsp hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  refine ⟨call_rsp hu, ?_, by rw [call_gpr (by decide), hdi], by rw [call_gpr (by decide), hsi],
    by rw [call_gpr (by decide), hdx], by rw [call_gpr (by decide), hcx],
    by rw [call_gpr (by decide), h8], by rw [call_gpr (by decide), h9], h0, h1, h2, h3, h4⟩
  simp only [gkLeak, gkA, gkS, hdom, hrand, hlen, hhead, Option.toList_some]
  rfl

private theorem call_pub {q : KeyPoint} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    attemptContract.pub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, i₁, j₁, k₁, l₁, m₁, n₁⟩ := call_view h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, i₂, j₂, k₂, l₂, m₂, n₂⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm, d₁.trans d₂.symm, e₁.trans e₂.symm,
    f₁.trans f₂.symm, g₁.trans g₂.symm, i₁.trans i₂.symm, j₁.trans j₂.symm, k₁.trans k₂.symm,
    l₁.trans l₂.symm, m₁.trans m₂.symm, n₁.trans n₂.symm⟩

private theorem call_ready {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    attemptContract.pre (callState q.inputs q.used u) ∧
      Covers (callReads q.inputs q.used ++ callWrites q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWrites q.inputs) u.wr ∧ u.gpr .rsp = q.inputs.sp - 40 := by
  obtain ⟨original, s, h, _, _, _, hr, ha, hm, k⟩ := h
  have hu : u.gpr .rsp = q.inputs.sp - 40 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp]; rfl
  exact ⟨call_attempt_pre (h.callFacts hr) h.rsp hu ha hm, call_covers_reads h hr k.2.1 k.2.2,
    call_covers_writes h k.2.2, hu⟩

theorem key_attempt_call_ct (v : RoundImpl) :
    RelCT isa (Two KeyCallCT) (attemptCall v) (fun _ _ => True) := by
  refine RelCT.callEx (attempt_correct v) (attempt_constantTime v) fun u₁ u₂ ⟨q, h₁, h₂⟩ => ?_
  obtain ⟨p₁, c₁, w₁, s₁⟩ := call_ready h₁
  obtain ⟨p₂, c₂, w₂, s₂⟩ := call_ready h₂
  exact ⟨_, _, _, _, p₁, p₂, call_pub h₁ h₂, c₁, w₁, c₂, w₂, s₁.trans s₂.symm⟩

theorem key_attempt_run_ct (v : RoundImpl) :
    RelCT isa (Two KeyReady) (attemptRun (attemptCall v)) (fun _ _ => True) := by
  unfold attemptRun
  apply frame_alloc_ct
  refine (RelCT.seq (two_piece [.r12, .rsp] key_allocated_pins (by taint_decide) arguments_ready)
    (key_attempt_call_ct v)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

end VG.Proof.Ffdh.X86_64.KeyGeneration
