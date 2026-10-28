module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCoreTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatchTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Prepared
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Timing
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Test
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareTimingHeader
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareTimingR2
import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Timing

/-! # Preparation with the run-time exponent, then the witnesses, leak only the iteration count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen VG.Proof.Dsa.X86

/-- The candidate's length `8 w` at header byte 4. -/
def Len (P : MillerRabinLoop.Parameters) (s : State) : Prop :=
  s.mem.readW (off P.g.W 4) 32 = BitVec.ofNat 32 (8 * P.g.w)

/-- Each run's inputs to preparation. -/
def InputsPair (P : MillerRabinLoop.Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (s t : State) : Prop :=
  (CandidatePrepare.Input P s ∧ Len P s) ∧ (CandidatePrepare.Input (P.withSecret other entropy) t ∧ Len P t)

theorem inputs_agree {P : MillerRabinLoop.Parameters} {other : Nat} {entropy : Spec.RsaKeyGen.Rand} {s t : State}
    (H : InputsPair P other entropy s t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact H.1.1.prepare.caller.sp.trans H.2.1.prepare.caller.sp.symm
  · exact BitVec.eq_of_toNat_eq (H.1.1.prepare.scratch.edi_toNat.trans H.2.1.prepare.scratch.edi_toNat.symm)

theorem inputs_keep {P : MillerRabinLoop.Parameters} {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (s t u z : State) (H : InputsPair P other entropy s t) (U : Fupd s u) (Z : Fupd t z) :
    InputsPair P other entropy u z :=
  ⟨⟨input_keep H.1.1 (U.keeps []) (by decide) (by decide) U.mem, by unfold Len; rw [U.mem]; exact H.1.2⟩,
    ⟨input_keep H.2.1 (Z.keeps []) (by decide) (by decide) Z.mem, by unfold Len; rw [Z.mem]; exact H.2.2⟩⟩

theorem width_run {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64) {s : State}
    (S : Scr s P.g.W P.g.L) (len : Len P s) :
    WP isa (.block VG.Impl.RsaKeyGen.X86.Candidate.width) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 P.g.w ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.width
  refine wp_movS (readSrc_sc S (d := 4) (by have := v.geometry.headerFit; omega)) fun a A _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun b B => WP.block_nil ⟨?_, B.mem.trans A.mem, A.keeps.trans B.keeps⟩
  rw [B.gpr, A.gpr, len]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem width_trace {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} :
    RelCT isa (InputsPair P other entropy) (.block VG.Impl.RsaKeyGen.X86.Candidate.width)
      (Candidate.WithValue (InputsPair P other entropy) (BitVec.ofNat 32 P.g.w)) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block VG.Impl.RsaKeyGen.X86.Candidate.width)
      (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  intro s t tr ur u z H E F
  obtain ⟨eu, Mu, Ku⟩ := wp_result (width_run v bound H.1.1.prepare.scratch H.1.2) E
  obtain ⟨ez, Mz, Kz⟩ := wp_result (width_run v bound H.2.1.prepare.scratch H.2.2) F
  refine ⟨(raw _ _ _ _ _ _ (inputs_agree H) E F).1, ⟨⟨⟨input_keep H.1.1 Ku (by decide) (by decide) Mu, ?_⟩,
    ⟨input_keep H.2.1 Kz (by decide) (by decide) Mz, ?_⟩⟩, eu, ez⟩⟩
  · unfold Len; rw [Mu]; exact H.1.2
  · unfold Len; rw [Mz]; exact H.2.2

theorem head_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64) (seed : P.seed = 64 * P.g.w - 1)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} :
    RelCT isa (InputsPair P other entropy) (VG.Impl.RsaKeyGen.X86.Candidate.prepareHead P.g.w name mont)
      (fun u z => Prepared P.g P.capacity P.p u ∧ Prepared P.g P.capacity P.p z) := by
  have G := v.geometry
  have raw : RelCT isa (fun s t => Prepare.InitialPair P.g P.capacity P.p s t)
      (VG.Impl.RsaKeyGen.X86.Candidate.prepareHead P.g.w name mont) (Pair P.g [.edi]) := by
    unfold VG.Impl.RsaKeyGen.X86.Candidate.prepareHead VG.Impl.RsaKeyGen.X86.PreparedR2.code
    exact RelCT.seq (Prepare.header_pair G v.length) (RelCT.seq
      (Prepare.r2_pairAt verified noSp stack G v.length bound (by have := G.minWidth; omega)
        (by have := G.minWidth; omega))
      (Constants.code_trace verified noSp stack G v.length))
  intro s t tr ur u z H E F
  have Is : Prepare.Input P.g P.candidate P.capacity P.p s := by have := H.1.1.prepare; rw [seed] at this; exact this
  have It : Prepare.Input P.g other P.capacity P.p t := by
    have := H.2.1.prepare
    change Prepare.Input P.g other P.capacity P.p t P.seed at this
    rw [seed] at this
    exact this
  refine ⟨(raw _ _ _ _ _ _ ⟨inputs_agree H, ⟨_, Is⟩, ⟨_, It⟩⟩ E F).1, ?_, ?_⟩
  · exact ⟨_, (wp_result (head_ok verified noSp stack G bound v.length Is) E).1⟩
  · exact ⟨_, (wp_result (head_ok verified noSp stack G bound v.length It) F).1⟩

theorem prepared_raw {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) {other : Nat} {entropy : Spec.RsaKeyGen.Rand} :
    RelCT isa (InputsPair P other entropy) (VG.Impl.RsaKeyGen.X86.Candidate.prepared name mont) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.prepared
  exact RelCT.seq (width_trace v bound) (RelCT.seq
    (Candidate.dispatch_trace (by omega) inputs_keep (head_trace verified noSp stack v bound seed) _
      (width_member width bound) widths_bounded)
    (MrExponentRt.code_trace v.geometry))

/-- Preparation with the run-time exponent: `CandidateTest.prepare_pair`. -/
theorem preparedRun_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) :
    RelCT isa (fun s t => InputsPair P other entropy s t ∧ P.iterations = (P.withSecret other entropy).iterations)
      (VG.Impl.RsaKeyGen.X86.Candidate.prepared name mont) (MillerRabinLoop.InitialPair P other entropy) := by
  intro s t tr ur u z ⟨H, iterations⟩ E G
  have trace := (prepared_raw verified noSp stack v width bound seed _ _ _ _ _ _ H E G).1
  obtain ⟨U, _, _, _⟩ := wp_result (prepared_ok verified noSp stack v width bound seed H.1.1 H.1.2) E
  obtain ⟨Z, _, _, _⟩ := wp_result (prepared_ok verified noSp stack w width bound seed H.2.1 H.2.2) G
  refine ⟨trace, ⟨U.prepared.ready.context, Z.prepared.ready.context, agree_regs fun r mem => ?_⟩,
    ⟨U.prepared, U.readable, U.entropy, U.randPtr, U.randLength, U.used⟩,
    ⟨Z.prepared, Z.readable, Z.entropy, Z.randPtr, Z.randLength, Z.used⟩, iterations⟩
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact U.prepared.ready.caller.sp.trans Z.prepared.ready.caller.sp.symm
  · exact (edi_value U.prepared.ready.context).trans (edi_value Z.prepared.ready.context).symm

/-- Preparation and the witnesses: `CandidateTest.core_trace` with the
exponent at the run-time width. -/
theorem body_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) (checks : P.checks = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks P.g.w)
    (bytes : P.bytes = 8 * P.g.w) (words : P.words = 2 * P.g.w)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} (w : (P.withSecret other entropy).Valid)
    (enough : P.start ≤ P.randLen) :
    RelCT isa (fun s t => InputsPair P other entropy s t ∧ P.iterations = (P.withSecret other entropy).iterations)
      (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round) (Pair P.g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.testBody
  exact RelCT.seq (preparedRun_pair montVerified montNoSp montStack v width bound seed w)
    (WitnessRt.codeRt_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
      ⟨bytes, words, checks⟩ w enough)

end VG.Proof.RsaKeyGen.X86.MrExponentRt
