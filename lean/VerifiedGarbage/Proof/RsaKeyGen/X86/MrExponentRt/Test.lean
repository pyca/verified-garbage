module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCore
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Prepared
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Loop
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpCode
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Preparation with the run-time exponent, then the witnesses, in the shared private frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen

/-- Preparation and the witnesses: `CandidateTest.core_ok` with the exponent
at the run-time width. -/
theorem body_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) (checks : P.checks = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks P.g.w)
    (bytes : P.bytes = 8 * P.g.w) (words : P.words = 2 * P.g.w) {s : State}
    (S : Prepare.Input P.g P.candidate P.capacity P.p s P.seed)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen)
    (len : s.mem.readW (off P.g.W 4) 32 = BitVec.ofNat 32 (8 * P.g.w)) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ MillerRabinLoop.Result P t ∧
      WorkspaceFrame P.g (CandidateTest.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.testBody
  refine WP.seq (WP.mono (prepared_ok montVerified montNoSp montStack v width bound seed
    ⟨S, readable, entropy, randPtr, randLength, used⟩ len) fun a ⟨A, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (WitnessRt.codeRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v ⟨bytes, words, checks⟩ A.prepared A.readable A.entropy A.randPtr A.randLength A.used enough)
    fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  refine ⟨T, result, ?_, (VG.X86.Frame.below_mono Fa (by decide) v.low).trans Ft, ?_⟩
  · exact (Wa.mono (fun _ mem => List.mem_append_left _ mem)).trans
      (Wt.mono (fun _ mem => List.mem_append_right _ mem))
  · exact (Ka.mono (by unfold Prepare.clob WitnessStep.clob; decide)).trans Kt

theorem tested_frame_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) (checks : P.checks = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks P.g.w)
    (bytes : P.bytes = 8 * P.g.w) (words : P.words = 2 * P.g.w) {s : State}
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
    (len : s.mem.readW (off P.g.W 4) 32 = BitVec.ofNat 32 (8 * P.g.w))
    (fit : 136 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ P.g.W.toNat ∨ P.g.W.toNat + P.g.L + 136 ≤ (s.gpr .esp).toNat)
    (randPrivateFar : (⟨P.rand.setWidth 64, P.randLen⟩ : Region).Disjoint (below (s.gpr .esp) 28)) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFrame.code
      (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round)) s fun t =>
      val32 t.mem P.g.W (P.g.array 0) P.g.words = P.candidate ∧ MillerRabinLoop.Result P t ∧
      WorkspaceFrame P.g (CandidateTest.ranges P.g) s.mem t.mem ∧
      Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 136] s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine CandidateFrame.code_full_ok (CandidateNoSp.testBody montNoSp roundNoSp montName roundName) S
    v.geometry.headerFit capacity fit separate ?_
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
  refine WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v width bound seed checks
    bytes words I
    (by
      rw [Ka.2.1, Ka.2.2]
      obtain ⟨r, mem, contains⟩ := readable
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp mem with mem | mem
      · exact List.mem_append_left _ mem
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ mem)) entropyA
    (by rw [Wa.read32 (by have := v.geometry.headerFit; omega) (by intro r mem; nomatch mem)]; exact randPtr)
    (by rw [w32, Wa.read32 (by have := v.geometry.headerFit; omega) (by intro r mem; nomatch mem)]; exact randLength)
    (by rw [w32, Wa.read32 (by have := v.geometry.headerFit; omega) (by intro r mem; nomatch mem)]; exact used) enough
    (by rw [Wa.read32 (by have := v.geometry.headerFit; omega) (by intro r mem; nomatch mem)]; exact len))
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

end VG.Proof.RsaKeyGen.X86.MrExponentRt
