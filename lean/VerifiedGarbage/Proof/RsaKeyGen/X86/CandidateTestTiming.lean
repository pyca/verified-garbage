module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCoreTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Timing
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTiming

import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Prepared
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareHeaderTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.R2Timing
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.ConstantsTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsTiming
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Timing
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
/-! # All prepared witnesses share one public private frame and one released iteration count -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MrExponentRt/TestTiming.lean`, which only this module imported.
section

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

/-- After the header, for the run's original inputs `s0`: what `head_ok` needs. -/
def Headed (P : MillerRabinLoop.Parameters) (s : State) : Prop :=
  ∃ s0, Prepare.Input P.g P.candidate P.capacity P.p s0 ∧ PreparedR2.Ready P.g P.candidate P.capacity P.p s ∧
    Outs P.g.W PrepareHeader.ranges s0.mem s.mem ∧ Keeps PrepareHeader.clob s0 s ∧
    word s.mem P.g.W 224 = BitVec.ofNat 64 (8 * (P.g.w + 2)) ∧ Len P s

def HeadedPair (P : MillerRabinLoop.Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (s t : State) : Prop :=
  Headed P s ∧ Headed (P.withSecret other entropy) t

theorem Headed.keep {P : MillerRabinLoop.Parameters} {s t : State} (H : Headed P s) {rs : List Reg}
    (K : Keeps rs s t) (sub : ∀ r ∈ rs, r ∈ PrepareHeader.clob) (M : t.mem = s.mem) : Headed P t := by
  obtain ⟨s0, I, R, O, Kh, stride, len⟩ := H
  have sp : .esp ∉ rs := fun mem => by have := sub _ mem; unfold PrepareHeader.clob at this; simp at this
  have edi : .edi ∉ rs := fun mem => by have := sub _ mem; unfold PrepareHeader.clob at this; simp at this
  refine ⟨s0, I, ⟨R.context.keepMem K edi M, by rw [M]; exact R.modulus,
    R.caller.keepFrame K sp (by rw [M]; exact Frame.refl _ _), R.scratch.of_keeps K edi sp⟩,
    by rw [M]; exact O, Kh.trans (K.mono sub), by rw [M]; exact stride, by unfold Len; rw [M]; exact len⟩

theorem headed_keep {P : MillerRabinLoop.Parameters} {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (s t u z : State) (H : HeadedPair P other entropy s t) (U : Fupd s u) (Z : Fupd t z) :
    HeadedPair P other entropy u z :=
  ⟨H.1.keep (U.keeps []) (fun _ mem => nomatch mem) U.mem, H.2.keep (Z.keeps []) (fun _ mem => nomatch mem) Z.mem⟩

/-- Header byte 4 is outside what the header writes. -/
theorem len_header {P : MillerRabinLoop.Parameters} {s t : State} (O : Outs P.g.W PrepareHeader.ranges s.mem t.mem)
    (len : Len P s) : Len P t := by
  have same := O.val32 (d := 4) (k := 1) (fun r mem => by
    simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with (rfl | rfl | rfl) | rfl <;> left <;> decide) (by decide)
  simp only [val32, Nat.mul_zero, Nat.add_zero] at same
  unfold Len at *
  rw [← len]
  exact BitVec.eq_of_toNat_eq same

theorem headed_ok {Q : MillerRabinLoop.Parameters} (G : Q.g.Valid) (length : Q.g.L = 8 * Q.capacity)
    (seed : Q.seed = 64 * Q.g.w - 1) {s : State} (I : CandidatePrepare.Input Q s) (len : Len Q s) :
    WP isa VG.Impl.RsaKeyGen.X86.HeaderRt.prepare s (Headed Q) := by
  have Ip : Prepare.Input Q.g Q.candidate Q.capacity Q.p s := by
    have := I.prepare
    rw [seed] at this
    exact this
  exact WP.mono (PrepareHeader.prepareRt_ok G Ip.scratch Ip.caller length Ip.candidate Ip.odd len)
    fun _ ⟨R, O, K, stride⟩ => ⟨s, Ip, R, O, K, stride, len_header O len⟩

theorem header_trace {P : MillerRabinLoop.Parameters} (v : P.Valid) (seed : P.seed = 64 * P.g.w - 1)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} :
    RelCT isa (InputsPair P other entropy) VG.Impl.RsaKeyGen.X86.HeaderRt.prepare (HeadedPair P other entropy) := by
  intro s t tr ur u z H E F
  exact ⟨(PrepareHeader.prepareRt_trace _ _ _ _ _ _ (inputs_agree H) E F).1,
    wp_result (headed_ok v.geometry v.length seed H.1.1 H.1.2) E,
    wp_result (headed_ok (Q := P.withSecret other entropy) v.geometry v.length seed H.2.1 H.2.2) F⟩

theorem headed_agree {P : MillerRabinLoop.Parameters} {other : Nat} {entropy : Spec.RsaKeyGen.Rand} {s t : State}
    (H : HeadedPair P other entropy s t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  obtain ⟨⟨_, _, Rs, _⟩, ⟨_, _, Rt, _⟩⟩ := H
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact Rs.caller.sp.trans Rt.caller.sp.symm
  · exact (edi_value Rs.context).trans (edi_value Rt.context).symm

theorem head_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand} :
    RelCT isa (HeadedPair P other entropy) (VG.Impl.RsaKeyGen.X86.Candidate.prepareHead name mont)
      (fun u z => Prepared P.g P.capacity P.p u ∧ Prepared P.g P.capacity P.p z) := by
  have G := v.geometry
  have raw : RelCT isa (fun s t => PreparedR2.Input P.g P.capacity P.p s ∧ PreparedR2.Input P.g P.capacity P.p t)
      (VG.Impl.RsaKeyGen.X86.Candidate.prepareHead name mont) (fun _ _ => True) := by
    unfold VG.Impl.RsaKeyGen.X86.Candidate.prepareHead
    exact RelCT.seq (PrepareRt.r2_trace verified noSp stack G v.length)
      (PrepareRt.constants_trace verified noSp stack G v.length)
  intro s t tr ur u z H E F
  obtain ⟨⟨s0, Is, Rs, Os, Ks, strides, _⟩, ⟨t0, It, Rt, Ot, Kt, stridet, _⟩⟩ := H
  refine ⟨(raw _ _ _ _ _ _ ⟨⟨_, Rs, Is.odd, Is.top⟩, ⟨_, Rt, It.odd, It.top⟩⟩ E F).1, ?_, ?_⟩
  · exact ⟨_, (wp_result (head_ok verified noSp stack G v.length Is Rs Os Ks strides) E).1⟩
  · exact ⟨_, (wp_result (head_ok verified noSp stack G v.length It Rt Ot Kt stridet) F).1⟩

theorem prepared_raw {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid)
    (seed : P.seed = 64 * P.g.w - 1) {other : Nat} {entropy : Spec.RsaKeyGen.Rand} :
    RelCT isa (InputsPair P other entropy) (VG.Impl.RsaKeyGen.X86.Candidate.prepared name mont) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.prepared
  exact RelCT.seq (header_trace v seed) (RelCT.seq (head_trace verified noSp stack v)
    (MrExponentRt.code_trace v.geometry))

/-- Preparation with the run-time exponent: `CandidateTest.prepare_pair`. -/
theorem preparedRun_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) :
    RelCT isa (fun s t => InputsPair P other entropy s t ∧ P.iterations = (P.withSecret other entropy).iterations)
      (VG.Impl.RsaKeyGen.X86.Candidate.prepared name mont) (MillerRabinLoop.InitialPair P other entropy) := by
  intro s t tr ur u z ⟨H, iterations⟩ E G
  have trace := (prepared_raw verified noSp stack v seed _ _ _ _ _ _ H E G).1
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
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
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
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidatePrivateInput.lean`, which only this module imported.
section

/-! # The single private call frame establishes every prepared-loop input -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem private_input {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (D : Drawn E eBytes pBytes entropy s)
    (minusOne : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1)
    (S : Scr t E.base E.size) (C : Caller E.geometry E.capacity (E.p - 28#32) t)
    (F : Frame [below E.p 28] s.mem t.mem) (K : Keeps [.edx] (allocFrame 28 s) t) :
    CandidatePrepare.Input (E.parameters entropy) t := by
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 28) :=
    (v.stackFar E.workspaceRegion (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right
      (below_sub (by decide) v.low)
  have randFar : E.randRegion.Disjoint (below E.p 28) :=
    (v.stackFar E.randRegion (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right
      (below_sub (by decide) v.low)
  have W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame F D.input.scratch.nowrap
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  have top : 2 ^ (64 * E.width - 1) ≤ candidateValue E entropy := by
    have lower := (candidate_shape v entropy).2.1
    have width := v.width_bounds.1
    have eqPower : 2 ^ (64 * E.width - 1) = 2 ^ (64 * E.width - 2) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    rw [eqPower]
    omega
  refine ⟨⟨S, C, ?_, ?_, candidate_odd v entropy, by change 1 < candidateValue E entropy; have := candidate_large v entropy; omega, top⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have value := W.val32 (v.geometry.arrayFit (j := 0) (by decide)) (by intro r mem; cases mem)
    rw [← Prepared.slot_eq] at value
    exact value.trans D.candidate
  · have value := W.val32 (v.geometry.arrayFit (j := 5) (by decide)) (by intro r mem; cases mem)
    rw [← Prepared.slot_eq] at value
    exact value.trans minusOne
  · rw [K.2.1, K.2.2]
    obtain ⟨r, mem, contains⟩ := D.input.memory.randRead
    refine ⟨r, ?_, contains⟩
    change r ∈ s.rd ++ (⟨(s.gpr .esp - 28#32).setWidth 64, 28⟩ :: s.wr)
    exact (List.mem_append.mp mem).elim (List.mem_append_left _) (fun known => List.mem_append_right _ (List.mem_cons_of_mem _ known))
  · change Spec.Rsa.bytesAt t.mem (E.rand.setWidth 64) E.randLength = entropy
    rw [VG.Proof.RsaKeyGen.frame_bytesAt F
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact randFar) (by have := v.randLengthFit; omega)]
    exact D.input.memory.entropy
  · exact (W.read32 (d := 28) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 28 + 4 ≤ E.size; omega)
      (by intro r mem; cases mem)).trans D.input.rand_eq
  · have word := W.read32 (d := 32) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 32 + 4 ≤ E.size; omega)
      (by intro r mem; cases mem)
    exact (congrArg BitVec.toNat word).trans (D.input.randLength_eq v)
  · have word := W.read32 (d := 152) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 152 + 4 ≤ E.size; omega)
      (by intro r mem; cases mem)
    change (t.mem.readW (off E.base 152) 32).toNat = 8 * E.width
    rw [v.length_eq]
    exact (congrArg BitVec.toNat word).trans D.used

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont.X86

structure TestPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop
    extends DrawnPair E eBytes pBytes qBytes rBytes sBytes s t where
  savedLeft : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E rBytes - 1
  savedRight : val32 t.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E sBytes - 1

theorem capacity_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (space : 44 ≤ size) :
    WP isa (.block [.mov .edx (.mem (sc 40))]) s fun t => Upd s t .edx (s.mem.readW (off base 40) 32) :=
  wp_movS (readSrc_sc S space) fun _ U _ => WP.block_nil U

/-- The candidate's length, kept inside the private frame. -/
theorem private_len {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (D : Drawn E eBytes pBytes entropy s) (F : Frame [below E.p 28] s.mem t.mem) (other : List Byte) :
    MrExponentRt.Len (E.parameters other) t := by
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 28) :=
    (v.stackFar E.workspaceRegion (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right
      (below_sub (by decide) v.low)
  have W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame F D.input.scratch.nowrap
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  change t.mem.readW (off E.geometry.W 4) 32 = BitVec.ofNat 32 (8 * E.width)
  rw [W.read32 (d := 4) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 4 + 4 ≤ E.size; omega)
    (by intro r mem; cases mem)]
  change s.mem.readW (off E.base (4 * 1)) 32 = _
  rw [D.input.header 1 (by decide)]
  change BitVec.ofNat 32 E.length = _
  rw [v.length_eq]

theorem private_pair {P : MillerRabinLoop.Parameters} {other : Nat} {entropy : List Byte} {s t : State}
    (I : CandidatePrepare.Input P s) (J : CandidatePrepare.Input (P.withSecret other entropy) t)
    (iterations : P.iterations = (P.withSecret other entropy).iterations) : CandidateTest.CorePair P other entropy s t := by
  refine ⟨?_, I, J, iterations⟩
  apply agree_regs
  intro r mem
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact I.prepare.caller.sp.trans J.prepare.caller.sp.symm
  · exact BitVec.eq_of_toNat_eq (I.prepare.scratch.edi_toNat.trans J.prepare.scratch.edi_toNat.symm)

theorem test_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (iterations : (E.parameters rBytes).iterations = (E.parameters sBytes).iterations)
    (enough : E.length ≤ E.randLength) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFrame.code
        (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round)) (fun _ _ => True) := by
  intro s t tr ur u z H A B
  have space : 256 ≤ E.size := v.geometry.headerFit
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block [.mov .edx (.mem (sc 40))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  cases A with
  | seq argsA frameA =>
    cases B with
    | seq argsB frameB =>
      have argsTrace := (raw _ _ _ _ _ _ H.toDrawnPair.inputs.agree argsA argsB).1
      have Ua := wp_result (capacity_ok H.left.input.scratch (by omega)) argsA
      have Ub := wp_result (capacity_ok H.right.input.scratch (by omega)) argsB
      have Da := H.left.keepMem v Ua.mem Ua.keeps (by decide) (by decide) Ua.syms
      have Db := H.right.keepMem v Ub.mem Ub.keeps (by decide) (by decide) Ub.syms
      have capA : _ := Ua.gpr.trans (H.left.input.header 10 (by decide))
      have capB : _ := Ub.gpr.trans (H.right.input.header 10 (by decide))
      cases frameA with
      | frame pushA bodyA popA =>
        cases frameB with
        | frame pushB bodyB popB =>
          have ea := alloc_some pushA
          have eb := alloc_some pushB
          subst ea eb
          cases bodyA with
          | seq storeA coreA =>
            cases bodyB with
            | seq storeB coreB =>
              have slotA := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity) Da.input.scratch (by rw [Da.input.stack]; exact v.low)
                (by rw [Da.input.stack]; exact v.workspaceStack) capA) storeA
              have slotB := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity) Db.input.scratch (by rw [Db.input.stack]; exact v.low)
                (by rw [Db.input.stack]; exact v.workspaceStack) capB) storeB
              obtain ⟨Sa, Ca, _, Fa, Ka⟩ := slotA
              obtain ⟨Sb, Cb, _, Fb, Kb⟩ := slotB
              rw [CandidateFrame.privateSp, Da.input.stack] at Ca
              rw [CandidateFrame.privateSp, Db.input.stack] at Cb
              rw [Da.input.stack] at Fa
              rw [Db.input.stack] at Fb
              have Ia := private_input v Da (by rw [Ua.mem]; exact H.savedLeft) Sa Ca Fa (Ka.mono (by decide))
              have Ib := private_input v Db (by rw [Ub.mem]; exact H.savedRight) Sb Cb Fb (Kb.mono (by decide))
              have initial : MrExponentRt.InputsPair (E.parameters rBytes) (candidateValue E sBytes) sBytes _ _ ∧
                  (E.parameters rBytes).iterations = ((E.parameters rBytes).withSecret (candidateValue E sBytes) sBytes).iterations :=
                ⟨⟨⟨Ia, private_len v Da Fa _⟩, ⟨Ib, private_len v Db Fb _⟩⟩, iterations⟩
              have coreTrace := (MrExponentRt.body_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
                (v.parameters_valid rBytes H.left.input.memory.entropyLength) v.width_bounds.1 v.width_bounds.2
                rfl rfl rfl rfl
                (v.parameters_valid sBytes H.right.input.memory.entropyLength) (by change 8 * E.width ≤ E.randLength; rw [v.length_eq]; exact enough)
                _ _ _ _ _ _ initial coreA coreB).1
              have storeRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.store (at_ .esp 24) .edx])
                  (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
              have storeTrace := (storeRaw _ _ _ _ _ _ (by
                apply agree_regs
                intro r mem
                obtain rfl := List.mem_singleton.mp mem
                rw [allocFrame_esp, allocFrame_esp, Da.input.stack, Db.input.stack]) storeA storeB).1
              refine ⟨?_, trivial⟩
              change _ ++ ([] ++ (_ ++ _) ++ []) = _ ++ ([] ++ (_ ++ _) ++ [])
              rw [argsTrace, storeTrace, coreTrace]

end VG.Proof.RsaKeyGen.X86.Candidate
