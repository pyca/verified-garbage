module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Parameters
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Finish
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Memory
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep
public import VerifiedGarbage.Proof.RsaKeyGen.MrCounts
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState

import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinOutcome
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Ranges
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCore
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpLoop
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack
/-! # The blinded loop and its result -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateTest.lean`, which only this module imported.
section

/-! # The shared private frame contains every prepared candidate call -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateTest
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen

theorem code_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64) {s : State}
    (S : Scr s P.g.W P.g.L) (capacity : w32 s.mem P.g.W 40 = P.capacity)
    (privateEq : P.p = CandidateFrame.privateSp s)
    (candidate : val32 s.mem P.g.W (P.g.array 0) P.g.words = P.candidate)
    (minusOne : val32 s.mem P.g.W (P.g.array 5) P.g.words = P.candidate - 1)
    (top : 2 ^ P.seed ≤ P.candidate)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen)
    (fit : 136 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ P.g.W.toNat ∨ P.g.W.toNat + P.g.L + 136 ≤ (s.gpr .esp).toNat)
    (randPrivateFar : (⟨P.rand.setWidth 64, P.randLen⟩ : Region).Disjoint (below (s.gpr .esp) 28)) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateTest.codeWith P.seed P.checks P.bytes P.words P.g.w montName mont roundName round) s fun t =>
      val32 t.mem P.g.W (P.g.array 0) P.g.words = P.candidate ∧ MillerRabinLoop.Result P t ∧
      WorkspaceFrame P.g (ranges P.g) s.mem t.mem ∧
      Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 136] s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateTest.codeWith
  refine CandidateFrame.code_full_ok (CandidateNoSp.coreWith montNoSp roundNoSp P.seed P.checks P.bytes P.words P.g.w montName roundName) S v.geometry.headerFit capacity fit separate ?_
  intro a Sa Ca _ Fa Ka
  have workspaceFar : (⟨P.g.W, P.g.L⟩ : Region).Disjoint (below (s.gpr .esp) 28) :=
    FilterStack.allocated_apart (by omega) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))
  have Wa : WorkspaceFrame P.g [] s.mem a.mem := by
    intro i index _
    exact Fa.bytes (R := ⟨P.g.W, P.g.L⟩)
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
      (by change P.g.L ≤ 2 ^ 64; have := S.nowrap; omega) index
  have I : Prepare.Input P.g P.candidate P.capacity P.p a P.seed := by
    refine ⟨Sa, ?_, ?_, ?_, v.odd, by have := v.large; omega, top⟩
    · rw [privateEq]; exact Ca
    · rw [Wa.val32 (v.geometry.arrayFit (by decide)) (by intro r mem; nomatch mem)]; exact candidate
    · rw [Wa.val32 (v.geometry.arrayFit (by decide)) (by intro r mem; nomatch mem)]; exact minusOne
  have entropyA : Spec.Rsa.bytesAt a.mem (P.rand.setWidth 64) P.randLen = P.entropy := by
    rw [frame_bytesAt Fa (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact randPrivateFar)
      (by have := v.randLenFit; omega)]
    exact entropy
  refine WP.mono (core_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v bound I
    (by
      rw [Ka.2.1, Ka.2.2]
      obtain ⟨r, mem, contains⟩ := readable
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp mem with mem | mem
      · exact List.mem_append_left _ mem
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ mem)) entropyA
    (by rw [Wa.read32 (by have := v.geometry.headerFit; omega) (by intro r mem; nomatch mem)]; exact randPtr)
    (by rw [w32, Wa.read32 (by have := v.geometry.headerFit; omega) (by intro r mem; nomatch mem)]; exact randLength)
    (by rw [w32, Wa.read32 (by have := v.geometry.headerFit; omega) (by intro r mem; nomatch mem)]; exact used) enough)
    fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  have outerFrame : Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 136] s.mem t.mem := by
    have first : Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 136] s.mem a.mem :=
      Fa.sub (by
        intro r mem; obtain rfl := List.mem_singleton.mp mem
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), below_sub (by decide) fit⟩)
    have second : Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 136] a.mem t.mem :=
      Ft.sub (by
        intro r mem
        simp only [List.mem_append, List.mem_singleton] at mem
        rcases mem with rfl | rfl
        · exact ⟨_, List.mem_cons_self, fun _ H => H⟩
        · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
          rw [privateEq]
          exact below_inner (by decide) fit)
    exact first.trans second
  refine ⟨T.ready.modulus.candidate, ?_, (Wa.mono (by intro r mem; nomatch mem)).trans Wt,
    outerFrame, FilterStack.freed_keeps ((Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt) (by unfold WitnessStep.clob; decide)⟩
  change MillerRabinLoop.Result P t
  exact result

end VG.Proof.RsaKeyGen.X86.CandidateTest
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86
open VG.Impl.Dsa.X86.ProbablePrime

theorem Memory.entropyLength {E : Environment} {c : Nat} {entropy : List Byte} {s : State}
    (M : Memory E c entropy s) : entropy.length = E.randLength := by
  rw [← M.entropy]
  exact VG.Proof.Bignum.bytesAt_length _ _ _

theorem tested_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateTest.codeWith (E.bits - 1) (Spec.Dsa.primeChecks E.bits)
      (8 * ((E.bits + 63) / 64)) E.words E.width montName mont roundName round) s fun a =>
      Input E c entropy a ∧ w32 a.mem E.base 168 = tag (E.parameters c entropy).test ∧
      (∀ b rest, (E.parameters c entropy).test = some (b, rest) →
        w32 a.mem E.base 152 = E.randLength - rest.length) ∧
      WorkFrame E s.mem a.mem ∧ Tail E s.mem a.mem ∧ Keeps WitnessStep.clob s a := by
  have P := v.parameters_valid odd length L.input.memory.entropyLength
  have shape := candidate_shape odd length (by have := v.bits.low; omega)
  have header := v.header
  have room := v.room
  have scratchEq : E.geometry.array 28 = E.scratch :=
    (VG.Proof.RsaKeyGen.X86.Prepared.slot_eq E.geometry 28).symm
  have gL : (E.parameters c entropy).g.L = E.size := rfl
  have inner : (below (s.gpr .esp) 28).Sub (below E.p 136) := by
    rw [L.input.stack]; exact below_sub (by decide) v.low
  change WP isa (VG.Impl.RsaKeyGen.X86.CandidateTest.codeWith (E.parameters c entropy).seed
    (E.parameters c entropy).checks (E.parameters c entropy).bytes (E.parameters c entropy).words
    (E.parameters c entropy).g.w montName mont roundName round) s _
  refine (WP.mono_syms (CandidateTest.code_ok montVerified montNoSp montStack roundVerified roundNoSp
    roundStack P v.width_high L.input.scratch L.input.capacity
    (by change E.p - 28#32 = s.gpr .esp - 28#32; rw [L.input.stack]) L.value L.minusOne
    (Nat.le_of_lt shape.2.1) L.input.memory.randRead L.input.memory.entropy L.input.randPtr
    L.input.randLength L.count (Nat.zero_le _) (by rw [L.input.stack]; exact v.low)
    (by rw [L.input.stack]; rcases v.workspaceStack with h | h; exact Or.inl h; exact Or.inr h)
    ((v.stackFar _ (List.mem_cons_of_mem _ List.mem_cons_self)).sub_right inner))
    fun a ⟨_, result, W, F, K⟩ syms => ?_)
  rw [L.input.stack] at F
  have WF : WorkFrame E s.mem a.mem := F
  have T : Tail E s.mem a.mem := by
    intro i lo hi
    exact W i hi (fun r mem => Or.inr (by have := test_ranges_before E.geometry r mem; rw [scratchEq] at this; omega))
  have read (d : Nat) (small : 28 ≤ d ∧ d + 4 ≤ 48) :
      a.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    W.read32 (by omega) (fun r mem => by have := test_ranges_header E.geometry r mem; omega)
  have Ia : Input E c entropy a := by
    refine ⟨L.input.scratch.of_keeps K (by decide), (K.1 .esp (by decide)).trans L.input.stack, ?_, ?_, ?_, ?_,
      L.input.memory.keep v K WF T (by rw [syms])⟩
    · rw [read 28 (by omega)]; exact L.input.randPtr
    · unfold w32; rw [read 32 (by omega)]; exact L.input.randLength
    · unfold w32; rw [read 40 (by omega)]; exact L.input.capacity
    · rw [read 44 (by omega)]; exact L.input.usedPtr
  have tagged : w32 a.mem E.base 168 = tag (E.parameters c entropy).test ∧
      ∀ b rest, (E.parameters c entropy).test = some (b, rest) →
        w32 a.mem E.base 152 = E.randLength - rest.length := by
    unfold MillerRabinLoop.Result at result
    change match (E.parameters c entropy).test with
      | none => w32 a.mem E.base 168 = 0
      | some (prime, rest) => w32 a.mem E.base 168 = (if prime then 1 else 3) ∧
          w32 a.mem E.base 152 = entropy.length - rest.length at result
    rcases same : (E.parameters c entropy).test with _ | ⟨prime, rest⟩
    · rw [same] at result
      exact ⟨result, fun _ _ bad => nomatch bad⟩
    · rw [same] at result
      refine ⟨by cases prime <;> simpa [tag] using result.1, ?_⟩
      intro b r eq
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj eq)
      rw [result.2, L.input.memory.entropyLength]
  exact ⟨Ia, tagged.1, tagged.2, WF, T, K⟩

theorem test_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits) :
    WP isa (test E.bits montName mont roundName round) s fun t =>
      Outputs E (E.parameters c entropy).test t ∧ MutableFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧
      Keeps WitnessStep.clob s t := by
  unfold test
  refine WP.seq (WP.mono (tested_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v L odd length)
    fun a ⟨Ia, status, counted, WF, T, K⟩ => ?_)
  refine WP.mono (finish_ok Ia (by have := v.header; omega) status counted) fun t ⟨out, Ft, Kt⟩ => ?_
  refine ⟨out, WF.mutable.trans (MutableFrame.of_used Ft), ?_, ?_⟩
  · refine T.trans ?_
    intro i lo hi
    apply Ft
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    have apart := v.usedWorkspace
    intro contains
    have fit := v.workspaceFit
    exact apart _ contains (Offset.contains_base E.base (by omega) (by omega))
  · exact K.trans (Kt.mono (by decide))

end VG.Proof.Dsa.X86.ProbablePrime
