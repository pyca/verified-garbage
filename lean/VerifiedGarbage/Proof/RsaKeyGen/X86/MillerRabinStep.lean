module

import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessAvailable
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory

/-! ### `RsaKeyGen.X86.MillerRabinExhausted`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.MillerRabinAfterDraw`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.MillerRabinPreserve`, which this module and modules that import it used -/

section

/-! # A witness step retains the entropy buffer and the outer loop's fixed metadata -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem step_header32 {g : Geometry} (v : g.Valid) {s t : Mem}
    (F : WorkspaceFrame g (WitnessStep.ranges g) s t) {d : Nat} (index : d = 28 ∨ d = 32 ∨ d = 200) :
    w32 t g.W d = w32 s g.W d := by
  apply congrArg BitVec.toNat
  apply F.read32 (by have := v.headerFit; omega_using [index, this])
  intro r mem
  simp only [WitnessStep.ranges, List.mem_append, List.mem_singleton] at mem
  rcases mem with (rfl | mem) | mem
  · rcases index with rfl | rfl | rfl <;> omega_using []
  · exact WitnessRound.ranges_apart32 (by rcases index with rfl | rfl | rfl <;> unfold WitnessRound.safeHeader <;> decide) r mem
  · simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl <;> rcases mem with (rfl | rfl) | rfl <;>
      simp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
        VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset] <;> omega_using []

theorem StateAt.next {P : Parameters} (v : P.Valid) {s t : State} {k n : Nat} (S : StateAt P k n s)
    (T : Prepare.Data P.g P.candidate P.capacity P.p t)
    (used : w32 t.mem P.g.W 152 = P.start + P.bytes * k + P.bytes)
    (rounds : w32 t.mem P.g.W 176 = k + 1)
    (uniform : w32 t.mem P.g.W 192 = (mrSB P.candidate P.bytes P.start P.entropy (k + 1)).2)
    (atLoop : MrLoopAt P.candidate P.checks P.twos.1 P.twos.2 P.bytes P.start P.entropy (k + 1) (n - 1))
    (W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem)
    (F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem)
    (K : Keeps WitnessStep.clob s t) : StateAt P (k + 1) (n - 1) t := by
  refine ⟨T, ?_, ?_, ?_, (step_header32 v.geometry W (Or.inr (Or.inl rfl))).trans S.randLength,
    ?_, rounds, uniform, (step_header32 v.geometry W (Or.inr (Or.inr rfl))).trans S.checks, atLoop⟩
  · rw [K.2.1, K.2.2]; exact S.readable
  · exact (frame_bytesAt F (by
      intro r mem
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact v.randSeparate
      · exact v.randStackFar) (by have := v.randLenFit; omega_using [this])).trans S.entropy
  · exact (BitVec.eq_of_toNat_eq (step_header32 v.geometry W (Or.inl rfl))).trans S.randPtr
  · rw [used, Nat.mul_succ]; omega_using []

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! ### `RsaKeyGen.X86.MillerRabinControl`, which this module and modules that import it used -/

section

/-! # Entropy exhaustion and the continuation flag of the blinded loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem word_equal4 (x : BitVec 32) : (x - 4#32 == 0#32) = decide (x.toNat = 4) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj, BitVec.toNat_sub]
  change (2 ^ 32 - 4 + x.toNat) % 2 ^ 32 = 0 ↔ x.toNat = 4
  have := x.isLt
  omega_using []

theorem again_ok {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L) :
    WP isa (.block again) s fun t =>
      t.zf = some (decide (w32 s.mem g.W 168 = 4)) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold again
  refine wp_movS (readSrc_sc S (by have := v.headerFit; omega_using [this])) fun a A _ =>
    wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.trans (T.keeps _)⟩
  rw [Z, A.gpr]
  change some (s.mem.readW (off g.W 168) 32 - 4#32 == 0#32) = _
  rw [word_equal4]

theorem exhausted_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) :
    WP isa (.block exhausted) s fun t =>
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 168 = 0 ∧
      Outside g.W 168 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  have head := v.headerFit
  unfold exhausted
  refine wp_movS rfl fun a A _ => ?_
  have Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega_using [head])) (Sa.write (by omega_using [head])) fun t T => WP.block_nil ?_
  have O : Outside g.W 168 4 s.mem t.mem := by
    rw [T.mem, A.mem]
    exact writeW32_outside _ _ _ (by decide)
  have K := A.keeps.widen (T.keeps [])
  exact ⟨S.keepGap v (by decide) (by decide) O K (by decide) (by decide),
    by rw [T.mem, w32_write_self, A.gpr]; rfl, O, K⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! ### `RsaKeyGen.X86.MillerRabinOutcome`, which this module and modules that import it used -/

section

/-! # Match native loop status with the reviewed primality result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.RsaKeyGen

def Result (P : Parameters) (s : State) : Prop :=
  match P.test with
  | none => w32 s.mem P.g.W 168 = 0
  | some (prime, rest) => w32 s.mem P.g.W 168 = (if prime then 1 else 3) ∧
      w32 s.mem P.g.W 152 = P.entropy.length - rest.length

theorem count_policy (P : Parameters) (k : Nat) :
    WitnessStatus.status
      (Proof.MillerRabin.Round.round P.candidate (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1)
      (k + 1) ((mrSB P.candidate P.bytes P.start P.entropy k).2 +
        (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).2.toNat) P.checks =
      if Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
          (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 then
        if goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) then 4 else 1
      else 3 := by
  have counts : (k + 1 < 16 ∨ (mrSB P.candidate P.bytes P.start P.entropy k).2 +
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).2.toNat < P.checks) ↔
      goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) := by
    unfold goS
    rw [mrSB_first, mrSB_uniform_next]
    unfold Spec.RsaKeyGen.blindedChecks
    omega_using []
  unfold WitnessStatus.status
  simp only [counts]
  rfl

theorem StateAt.noEntropy {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (short : ¬ P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    n = 0 ∧ P.test = none :=
  mrLoopAt_short S.atLoop v.witnessBytes (by have := v.narrow; have := v.two; omega_arith)
    (by rw [v.entropyLength]; exact short)

theorem StateAt.failed {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen)
    (failed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 = false) :
    n = 0 ∧ P.test =
      some (false, P.entropy.drop (P.start + P.bytes * k + P.bytes)) :=
  mrLoopAt_fail S.atLoop v.witnessBytes (by have := v.narrow; have := v.two; omega_arith)
    (by rw [v.entropyLength]; exact enough) failed

theorem StateAt.accepted {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen)
    (passed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 = true)
    (done : ¬ goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1))) :
    n = 0 ∧ P.test =
      some (true, P.entropy.drop (P.start + P.bytes * k + P.bytes)) :=
  mrLoopAt_done S.atLoop v.witnessBytes (by have := v.narrow; have := v.two; omega_arith)
    (by rw [v.entropyLength]; exact enough) passed done

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! # A passing witness continues or accepts; a failing witness rejects -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MillerRabinDraw.lean`, which only this module imported.
section

/-! # A native witness draw advances the reviewed loop's exact counters and status -/

section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem draw_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessStep.codeAt P.bytes P.words P.g.w montName mont roundName round) s fun t =>
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
  refine WP.mono (WitnessStep.codeAt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v.geometry
    v.two v.narrow v.wide v.four
    v.length S.prepared S.randPtr S.used v.randFit v.randLenFit enough S.readable v.randSeparate v.odd (by have := v.large; omega)
    v.shape counts.1 counts.2 v.low v.stackFar v.lengthFar) fun t ⟨T, used, rounds, uniform, status, W, F, K⟩ => ?_
  rw [S.rounds] at rounds
  rw [S.sample enough, S.uniform, ← mrSB_uniform_next] at uniform
  rw [S.sample enough, S.rounds, S.uniform, S.checks, count_policy] at status
  exact ⟨T, used, rounds, uniform, status, W, F, K⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

def Outcome (P : Parameters) (k n : Nat) (t : State) : Prop :=
  (isa.eval .e t = some false ∧ n = 0 ∧ Result P t) ∨
    (isa.eval .e t = some true ∧ 0 < n ∧ StateAt P (k + 1) (n - 1) t)

theorem draw_again_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (.seq (VG.Impl.RsaKeyGen.X86.WitnessStep.codeAt P.bytes P.words P.g.w montName mont roundName round) (.block again)) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.seq (WP.mono (draw_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v S enough)
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
      omega_using [bound]
  | true =>
    by_cases more : goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1))
    · have next := mrLoopAt_next S.atLoop v.witnessBytes
        (by have := v.narrow; have := v.two; omega_arith)
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
        omega_using [bound]

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! # Too little entropy terminates the primality test with its specified failure -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem exhausted_again_ok {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (short : ¬ P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (.seq (.block exhausted) (.block again)) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have failed := S.noEntropy v short
  refine WP.seq (WP.mono (exhausted_ok v.geometry S.prepared) fun a ⟨A, statusA, Oa, Ka⟩ => ?_)
  refine WP.mono (again_ok v.geometry A.ready.scratch) fun t ⟨Z, mem, Kt⟩ => ?_
  have K : Keeps WitnessStep.clob s t := (Ka.mono (by unfold WitnessStep.clob; decide)).widen Kt
  have T := A.keepHeader v.geometry (d := 128) (bytes := 0) (by decide) (by decide)
    (show Outside P.g.W 128 0 a.mem t.mem from by rw [mem]; exact Outside.refl _ _ _ _) Kt (by decide) (by decide)
  have Ot : Outside P.g.W 168 4 s.mem t.mem := by rw [mem]; exact Oa
  have W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem :=
    WorkspaceFrame.of_outs S.prepared.ready.scratch.nowrap (Outs.of_outside Ot
      (by simp [WitnessStep.ranges, WitnessCount.ranges, VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset]))
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ot (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.geometry.headerFit; omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  refine ⟨T, Or.inl ⟨?_, failed.1, ?_⟩, W, F, K⟩
  · change t.zf = some false
    rw [Z, statusA]; rfl
  · unfold Result
    rw [failed.2, mem]
    exact statusA

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! # A complete blinded-loop step either stops or decreases its specified iteration count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem step_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (stepAt P.bytes P.words P.g.w montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have usedBound : P.start + P.bytes * k ≤ P.randLen := by
    have := S.atLoop.used
    rw [v.entropyLength] at this
    exact this
  unfold stepAt
  refine WP.seq (WP.mono (WitnessAvailable.codeAt_ok S.prepared.ready.scratch v.geometry.headerFit
    (by have := v.geometry.maxWidth; have := v.wide; omega_arith) S.randLength S.used usedBound) fun a ⟨CF, mem, Ka⟩ => ?_)
  have A := S.keepMem v mem Ka (by decide) (by decide)
  have condition : isa.eval .b a = some (decide (¬ P.start + P.bytes * k + P.bytes ≤ P.randLen)) := by
    change a.cf = _
    rw [CF]
    congr 1
    apply decide_eq_decide.mpr
    change (P.randLen - (P.start + P.bytes * k) < P.bytes) ↔ ¬ P.start + P.bytes * k + P.bytes ≤ P.randLen
    omega_using [usedBound]
  refine WP.seq ?_
  by_cases enough : P.start + P.bytes * k + P.bytes ≤ P.randLen
  · refine WP.ite false (by rw [condition]; simp only [enough, not_true_eq_false, decide_false])
      (fun impossible => nomatch impossible) (fun _ => ?_)
    apply WP.seq_iff.mp
    refine WP.mono (draw_again_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v A enough)
      fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
  · refine WP.ite true (by rw [condition]; simp only [enough, not_false_eq_true, decide_true])
      (fun _ => ?_) (fun impossible => nomatch impossible)
    apply WP.seq_iff.mp
    refine WP.mono (exhausted_again_ok v A enough) fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
