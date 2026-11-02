module

import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.SampleTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Loop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStepTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTimingState
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTimingStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessCountTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessInput
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Body
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRoundTiming
public import VerifiedGarbage.Proof.MillerRabin.Contract

/-! # The witness loop at the run-time width reveals only its consumed entropy length

`MillerRabinLoop.code_trace` for the run-time loop: each witness's draw is
checked in segments (`drawn_pair`), the rest as for a fixed width. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG.Proof.RsaKeyGen.X86.WitnessRound (Work WorkPair)
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop (exhausted again)
open VG.Impl.RsaKeyGen.X86.WitnessRt (drawn advance available checks)

theorem drawn_pair {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {input : Import.Geometry}
    (count : input.count = g.words) :
    RelCT isa (WitnessRound.InitialPair g capacity p input) drawn (WorkPair g capacity p) := by
  refine (RelCT.seq (load_trace v count) (sample_trace v)).mono (fun _ _ H => ⟨H.2.1, H.2.2⟩)
    fun u z ⟨U, Z⟩ => ⟨⟨U.context, Z.context, agree_regs fun r mem => ?_⟩, U, Z⟩
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact U.sp.trans Z.sp.symm
  · exact (edi_value U.context).trans (edi_value Z.context).symm

theorem advance_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block advance)
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block advance) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem available_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block available)
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block available) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem checks_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block checks)
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block checks) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem availableRt_ok {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat}
    (S : StateAt P k n s) :
    WP isa (.block available) s fun t =>
      StateAt P k n t ∧ isa.eval .b t = some (decide (P.randLen - (P.start + P.bytes * k) < P.bytes)) := by
  have usedBound : P.start + P.bytes * k ≤ P.randLen := by
    have := S.atLoop.used; rw [v.entropyLength] at this; exact this
  refine WP.mono (available_ok v.geometry S.prepared.ready.scratch S.prepared.ready.context S.randLength S.used
    usedBound) fun t ⟨CF, mem, K⟩ => ?_
  refine ⟨S.keepMem v mem K (by decide) (by decide), ?_⟩
  rw [← Fx.bytes] at CF
  exact CF

theorem availableRt_pair {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat}
    {entropy : Spec.RsaKeyGen.Rand} (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (.block available) (AvailablePair P other entropy k n) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := available_raw _ _ _ _ _ _ H.1.2.2 E G
  obtain ⟨U, Cu⟩ := wp_result (availableRt_ok v Fx H.2.1) E
  obtain ⟨Z, Cz⟩ := wp_result (availableRt_ok w ⟨Fx.bytes, Fx.words, Fx.checks⟩ H.2.2) G
  exact ⟨trace, ⟨⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩, U, Z⟩, Cu, Cz⟩

theorem round_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {input : Import.Geometry}
    (count : input.count = g.words) (length : g.L = 8 * capacity) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (WitnessRound.InitialPair g capacity p input) (VG.Impl.RsaKeyGen.X86.WitnessRt.round montName mont roundName round)
      (Pair g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.round
  exact RelCT.seq (drawn_pair v count) (RelCT.seq (WitnessRound.store_pair v)
    (RelCT.seq (WitnessRound.convert_pair montVerified montNoSp montStack v length)
      (RoundCall.code_trace roundVerified roundNoSp roundStack v length fit far lengthFar)))

theorem advance_pair {g : Geometry} (v : g.Valid) {capacity used randLen : Nat} {p rand : BitVec 32}
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + 8 * g.w ≤ randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩) :
    RelCT isa (WitnessStep.InitialPair g capacity p rand used randLen) (.block advance)
      (WitnessRound.InitialPair g capacity p (WitnessInput.geometryAt g rand used g.words)) := by
  have positive := v.minWidth
  have bound := v.maxWidth
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := advance_raw _ _ _ _ _ _ H.1.2.2 E G
  have post {a : State} (I : WitnessStep.Initial g capacity p rand used randLen a) :
      WP isa (.block advance) a fun b =>
        WitnessRound.Initial g capacity p (WitnessInput.geometryAt g rand used g.words) b ∧
        b.gpr .esi = rand + BitVec.ofNat 32 used := by
    obtain ⟨c, S, source, consumed, odd, large, shape, _, _, readable⟩ := I
    refine WP.mono (advance_ok v S source consumed (by omega))
      fun b ⟨B, ptr, _, _, K⟩ => ?_
    have readB : InRegions (b.rd ++ b.wr) (rand.setWidth 64) randLen := by
      rw [K.2.1, K.2.2]; exact readable
    exact ⟨⟨c, B, odd, large, shape, WitnessInput.context_okAt (used := used) (count := g.words) v B.ready.scratch
      randFit (by unfold Geometry.words; omega) (by unfold Geometry.words; omega) (by unfold Geometry.words; omega)
      readB separate,
      ptr, (WitnessInput.destination_pointer v B.ready.scratch).symm⟩, ptr⟩
  obtain ⟨U, sourceU⟩ := wp_result (post H.2.1) E
  obtain ⟨Z, sourceZ⟩ := wp_result (post H.2.2) G
  obtain ⟨cu, Du, ou, lu, hu, Cu, su, du⟩ := U
  obtain ⟨cz, Dz, oz, lz, hz, Cz, sz, dz⟩ := Z
  have registers : ∀ r ∈ ([.edi, .esi] : List Reg), u.gpr r = z.gpr r := by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact round_regs agree (by decide)
    · rw [sourceU, sourceZ]
  exact ⟨trace, ⟨Du.ready.context, Dz.ready.context, round_add_regs (round_forget agree) registers⟩,
    ⟨cu, Du, ou, lu, hu, Cu, su, du⟩, ⟨cz, Dz, oz, lz, hz, Cz, sz, dz⟩⟩

theorem body_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity used randLen : Nat} {p rand : BitVec 32}
    (length : g.L = 8 * capacity)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + 8 * g.w ≤ randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (WitnessStep.InitialPair g capacity p rand used randLen)
      (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round) (Pair g [.edi]) := by
  have raw : RelCT isa (WitnessStep.InitialPair g capacity p rand used randLen)
      (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
    unfold VG.Impl.RsaKeyGen.X86.WitnessRt.body
    refine RelCT.seq (advance_pair v randFit randLenFit enough separate) (RelCT.seq
      (round_trace (input := WitnessInput.geometryAt g rand used g.words) montVerified montNoSp
        montStack roundVerified roundNoSp roundStack v rfl length fit far lengthFar) ?_)
    exact WitnessCount.code_trace.mono (fun _ _ H => H.2.2) (fun _ _ H => H)
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := raw _ _ _ _ _ _ H E G
  have post {a : State} (I : WitnessStep.Initial g capacity p rand used randLen a) :
      WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round) a (Context g) := by
    obtain ⟨c, S, source, consumed, odd, large, shape, roundsFit, uniformFit, readable⟩ := I
    exact WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v
      length S source consumed randFit randLenFit enough readable separate odd large (by rw [shape]; omega) roundsFit
      uniformFit fit far lengthFar) fun _ R => R.1.ready.context
  exact ⟨trace, wp_result (post H.2.1) E, wp_result (post H.2.2) G, agree⟩

theorem branchRt_raw {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (AvailablePair P other entropy k n)
      (.ite .b (.block exhausted) (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round))
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  refine VG.RelCT.ite (fun _ _ H => H.2.1.trans H.2.2.symm)
    (exhausted_raw.mono (fun _ _ H => H.1.1.1.2.2) (fun _ _ H => H)) ?_
  intro s t tr ur u z H E G
  have enough : P.start + P.bytes * k + P.bytes ≤ P.randLen := by
    by_contra short
    have bound := H.1.1.2.1.atLoop.used
    rw [v.entropyLength] at bound
    have small : P.randLen - (P.start + P.bytes * k) < P.bytes := by omega
    have condition := H.1.2.1
    rw [H.2, decide_eq_true small] at condition
    cases condition
  have pre : WitnessStep.InitialPair P.g P.capacity P.p P.rand (P.start + P.bytes * k) P.randLen s t :=
    ⟨H.1.1.1, Fx.words ▸ H.1.1.2.1.stepInitial v, Fx.words ▸ H.1.1.2.2.stepInitial w⟩
  obtain ⟨trace, pair⟩ := body_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v.geometry v.length v.randFit v.randLenFit (by rw [← Fx.bytes]; exact enough) v.randSeparate v.low v.stackFar
    v.lengthFar _ _ _ _ _ _ pre E G
  exact ⟨trace, pair.2.2⟩

theorem stepRt_raw {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.step
  exact RelCT.seq (availableRt_pair v Fx w k n)
    (RelCT.seq (branchRt_raw montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx w k n) again_raw)

theorem stepRt_pair {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round)
      (fun s t => Pair P.g [.edi] s t ∧ Outcome P k n s ∧ Outcome (P.withSecret other entropy) k n t) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := stepRt_raw montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx w k n _ _ _ _ _ _ H E G
  obtain ⟨U, Ou, _, _, _⟩ := wp_result
    (stepRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx H.2.1) E
  obtain ⟨Z, Oz, _, _, _⟩ := wp_result
    (stepRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack w ⟨Fx.bytes, Fx.words, Fx.checks⟩ H.2.2) G
  exact ⟨trace, ⟨U.ready.context, Z.ready.context, agree⟩, Ou, Oz⟩

theorem loopRt_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (.loop (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round) .e) (Pair P.g [.edi]) := by
  let Inv : Nat → State → State → Prop := fun q s t => ∃ k n, q = n + 1 ∧ LoopPair P other entropy k n s t
  have run : RelCT isa (Inv (n + 1)) (.loop (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round) .e) (Pair P.g [.edi]) := by
    refine RelCT.loop (M := isa) Inv ?_ (n + 1)
    rintro q s t tr ur u z ⟨i, j, rfl, H⟩ E G
    obtain ⟨trace, pair, Ou, Oz⟩ := stepRt_pair montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx w i j _ _ _ _ _ _ H E G
    rcases Ou with ⟨Eu, zeroU, _⟩ | ⟨Eu, positiveU, U⟩ <;>
      rcases Oz with ⟨Ez, zeroZ, _⟩ | ⟨Ez, positiveZ, Z⟩
    · refine ⟨trace, Eu.trans Ez.symm, fun _ => pair, ?_⟩
      intro continuing
      rw [Eu] at continuing
      cases continuing
    · omega
    · omega
    · refine ⟨trace, Eu.trans Ez.symm, ?_, ?_⟩
      · intro done
        rw [Eu] at done
        cases done
      · intro _
        exact ⟨j, by omega, i + 1, j - 1, by omega, pair, U, Z⟩
  exact run.mono (fun _ _ H => ⟨k, n, rfl, H⟩) (fun _ _ H => H)

theorem initRt_pair {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (.block VG.Impl.RsaKeyGen.X86.WitnessRt.checks)
      (LoopPair P other entropy 0 P.iterations) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := checks_raw _ _ _ _ _ _ H.1.2.2 E G
  obtain ⟨S, readS, bytesS, ptrS, lenS, usedS⟩ := H.2.1
  obtain ⟨T, readT, bytesT, ptrT, lenT, usedT⟩ := H.2.2.1
  obtain ⟨U, _, _, _⟩ := wp_result (initRt_ok v Fx S readS bytesS ptrS lenS usedS enough) E
  obtain ⟨Z, _, _, _⟩ := wp_result (initRt_ok w ⟨Fx.bytes, Fx.words, Fx.checks⟩ T readT bytesT ptrT lenT usedT enough) G
  have iters := H.2.2.2
  change P.iterations = (P.withSecret other entropy).iterations at iters
  change StateAt (P.withSecret other entropy) 0 (P.withSecret other entropy).iterations z at Z
  rw [← iters] at Z
  exact ⟨trace, ⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩, U, Z⟩

theorem codeRt_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (VG.Impl.RsaKeyGen.X86.WitnessRt.code montName mont roundName round) (Pair P.g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.code
  exact RelCT.seq (initRt_pair v Fx w enough)
    (loopRt_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx w 0 P.iterations)

end VG.Proof.RsaKeyGen.X86.WitnessRt
