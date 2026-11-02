module

import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Body
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Proof.RsaKeyGen.MrCounts
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinAfterDraw
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinExhausted
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinControl
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinPreserve
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessChecks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep

/-! # The blinded witness loop at the run-time width

`MillerRabinLoop.code_ok` for the loop whose width, witness octets and
required tests come from the prepared header: RSA's parameters (`Fixed`). -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop (exhausted again)

/-- The parameters the run-time loop computes from the width: RSA's. -/
structure Fixed (P : Parameters) : Prop where
  bytes : P.bytes = 8 * P.g.w
  words : P.words = 2 * P.g.w
  checks : P.checks = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks P.g.w

theorem drawRt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧
      w32 t.mem P.g.W 152 = P.start + P.bytes * k + P.bytes ∧ w32 t.mem P.g.W 176 = k + 1 ∧
      w32 t.mem P.g.W 192 = (mrSB P.candidate P.bytes P.start P.entropy (k + 1)).2 ∧
      w32 t.mem P.g.W 168 =
        (if Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
            (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 then
          if goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) then 4 else 1
        else 3) ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have counts := S.countFit v
  refine WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v.geometry
    v.length S.prepared S.randPtr S.used v.randFit v.randLenFit (by rw [← Fx.bytes]; exact enough) S.readable
    v.randSeparate v.odd (by have := v.large; omega) (by rw [v.shape, Fx.words]; omega) counts.1 counts.2 v.low
    v.stackFar v.lengthFar) fun t ⟨T, used, rounds, uniform, status, W, F, K⟩ => ?_
  rw [← Fx.bytes] at used uniform status
  rw [S.rounds] at rounds
  rw [S.sample enough, S.uniform, ← mrSB_uniform_next] at uniform
  rw [S.sample enough, S.rounds, S.uniform, S.checks, count_policy] at status
  exact ⟨T, used, rounds, uniform, status, W, F, K⟩

theorem drawRt_again_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (.seq (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round) (.block again)) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.seq (WP.mono (drawRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx S enough)
    fun a ⟨A, usedA, roundsA, uniformA, statusA, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (again_ok v.geometry A.ready.scratch) fun t ⟨Z, mem, Kt⟩ => ?_
  have T := A.keepHeader v.geometry (d := 128) (bytes := 0) (by decide) (by decide)
    (show Outside P.g.W 128 0 a.mem t.mem from by rw [mem]; exact Outside.refl _ _ _ _) Kt (by decide) (by decide)
  have W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem := by rw [mem]; exact Wa
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem := by rw [mem]; exact Fa
  refine ⟨T, ?_, W, F, Ka.widen Kt⟩
  have ev : isa.eval .e t = some (decide (w32 a.mem P.g.W 168 = 4)) := Z
  cases passed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 with
  | false =>
    have failed := S.failed v enough passed
    simp only [passed] at statusA
    refine Or.inl ⟨?_, failed.1, ?_⟩
    · rw [ev, statusA]; rfl
    · unfold Result
      rw [failed.2, mem]
      refine ⟨statusA, ?_⟩
      rw [usedA, List.length_drop]
      have bound := enough
      rw [← v.entropyLength] at bound
      omega
  | true =>
    by_cases more : goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1))
    · have next := mrLoopAt_next S.atLoop v.witnessBytes
        (by have := v.narrow; have := v.two; omega)
        (by rw [v.entropyLength]; exact enough) passed more
      simp only [passed, ↓reduceIte, more] at statusA
      have nextState := StateAt.next v S A usedA roundsA uniformA next.2 Wa Fa Ka
      refine Or.inr ⟨?_, next.1, nextState.keepMem v mem Kt (by decide) (by decide)⟩
      rw [ev, statusA]; rfl
    · have done := S.accepted v enough passed more
      simp only [passed, ↓reduceIte, more] at statusA
      refine Or.inl ⟨?_, done.1, ?_⟩
      · rw [ev, statusA]; rfl
      · unfold Result
        rw [done.2, mem]
        refine ⟨statusA, ?_⟩
        rw [usedA, List.length_drop]
        have bound := enough
        rw [← v.entropyLength] at bound
        omega

theorem stepRt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have usedBound : P.start + P.bytes * k ≤ P.randLen := by
    have := S.atLoop.used
    rw [v.entropyLength] at this
    exact this
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.step
  refine WP.seq (WP.mono (available_ok v.geometry S.prepared.ready.scratch S.prepared.ready.context S.randLength
    S.used usedBound) fun a ⟨CF, mem, Ka⟩ => ?_)
  have A := S.keepMem v mem Ka (by decide) (by decide)
  have condition : isa.eval .b a = some (decide (¬ P.start + P.bytes * k + P.bytes ≤ P.randLen)) := by
    change a.cf = _
    rw [CF]
    congr 1
    apply decide_eq_decide.mpr
    rw [← Fx.bytes]
    omega
  refine WP.seq ?_
  by_cases enough : P.start + P.bytes * k + P.bytes ≤ P.randLen
  · refine WP.ite false (by rw [condition]; simp only [enough, not_true_eq_false, decide_false])
      (fun impossible => nomatch impossible) (fun _ => ?_)
    apply WP.seq_iff.mp
    refine WP.mono (drawRt_again_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx A enough)
      fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
  · refine WP.ite true (by rw [condition]; simp only [enough, not_false_eq_true, decide_true])
      (fun _ => ?_) (fun impossible => nomatch impossible)
    apply WP.seq_iff.mp
    refine WP.mono (exhausted_again_ok v A enough) fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

theorem initRt_ok {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State}
    (S : Prepare.Data P.g P.candidate P.capacity P.p s)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen) :
    WP isa (.block VG.Impl.RsaKeyGen.X86.WitnessRt.checks) s fun t =>
      StateAt P 0 (itersOf P.bytes P.entropy.length
        (shapeOf P.test) P.start - 1) t ∧
      WorkspaceFrame P.g WitnessChecks.ranges s.mem t.mem ∧ Frame [⟨P.g.W, P.g.L⟩] s.mem t.mem ∧
      Keeps [.eax, .ecx] s t := by
  refine WP.mono (checks_ok v.geometry S) fun t ⟨T, roundsT, uniformT, checksT, O, K⟩ => ?_
  rw [← Fx.checks] at checksT
  have rangesFit : ∀ r ∈ WitnessChecks.ranges, r.1 + r.2 ≤ P.g.L := by
    intro r mem
    simp only [WitnessChecks.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> have := v.geometry.headerFit <;> omega
  have W := WorkspaceFrame.of_outs S.ready.scratch.nowrap O
  have F := workspaceGlobalFrame O rangesFit
  have hdr {d : Nat} (bound : d + 4 ≤ 176) : w32 t.mem P.g.W d = w32 s.mem P.g.W d := by
    apply congrArg BitVec.toNat
    apply W.read32 (by have := v.geometry.headerFit; omega)
    intro r mem
    simp only [WitnessChecks.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> left <;> omega
  have primeAt := mrLoopAt_zero (ch := P.checks) (a := P.twos.1) (m := P.twos.2) (s := P.start) v.witnessBytes
    (by have := v.narrow; have := v.two; omega)
    (by rw [v.entropyLength]; exact enough)
  refine ⟨⟨T, ?_, ?_, ?_, (hdr (by decide)).trans randLength,
    by simpa only [Nat.mul_zero, Nat.add_zero] using (hdr (d := 152) (by decide)).trans used,
    roundsT, uniformT, checksT, primeAt⟩, W, F, K⟩
  · rw [K.2.1, K.2.2]; exact readable
  · exact (frame_bytesAt F (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.randSeparate)
      (by have := v.randLenFit; omega)).trans entropy
  · exact (BitVec.eq_of_toNat_eq (hdr (d := 28) (by decide))).trans randPtr

theorem loopRt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (.loop (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round) .e) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Result P t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  let Inv : Nat → State → Prop := fun q t => ∃ i j, q = j + 1 ∧ StateAt P i j t ∧
    WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
    Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t
  have initial : Inv (n + 1) s := ⟨k, n, rfl, S, WorkspaceFrame.refl _ _ _, Frame.refl _ _, Keeps.refl _ _⟩
  refine WP.loop (M := isa) Inv ?_ (n + 1) s initial
  rintro q a ⟨i, j, rfl, A, Wa, Fa, Ka⟩
  refine WP.mono (stepRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx A)
    fun t ⟨T, outcome, Wt, Ft, Kt⟩ => ?_
  rcases outcome with ⟨done, _, result⟩ | ⟨again, positive, next⟩
  · exact Or.inl ⟨done, T, result, Wa.trans Wt, Fa.trans Ft, Ka.trans Kt⟩
  · exact Or.inr ⟨again, j, by omega, i + 1, j - 1, by omega, next, Wa.trans Wt, Fa.trans Ft, Ka.trans Kt⟩

theorem codeRt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State}
    (S : Prepare.Data P.g P.candidate P.capacity P.p s)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.code montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Result P t ∧
      WorkspaceFrame P.g (MillerRabinLoop.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.code
  refine WP.seq (WP.mono (initRt_ok v Fx S readable entropy randPtr randLength used enough)
    fun a ⟨A, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (loopRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx A)
    fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  have Wsa := Wa.mono (fun r mem => List.mem_append_left _ mem : ∀ r ∈ WitnessChecks.ranges, r ∈ MillerRabinLoop.ranges P.g)
  have Wat := Wt.mono (fun r mem => List.mem_append_right _ mem : ∀ r ∈ WitnessStep.ranges P.g, r ∈ MillerRabinLoop.ranges P.g)
  exact ⟨T, result, Wsa.trans Wat, (Fa.mono (fun r mem => List.mem_append_left _ mem)).trans Ft,
    (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessRt
