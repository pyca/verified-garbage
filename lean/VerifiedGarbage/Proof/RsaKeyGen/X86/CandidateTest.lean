module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCore
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpLoop
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack

/-! # The shared private frame contains every prepared candidate call -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateTest
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen

theorem code_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64) {s : State}
    (S : Scr s P.g.W P.g.L) (capacity : w32 s.mem P.g.W 40 = P.capacity)
    (privateEq : P.p = CandidateFrame.privateSp s)
    (candidate : val32 s.mem P.g.W (P.g.array 0) P.g.words = P.candidate)
    (minusOne : val32 s.mem P.g.W (P.g.array 5) P.g.words = P.candidate - 1)
    (top : 2 ^ (64 * P.g.w - 1) ≤ P.candidate)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.bytes) (enough : P.bytes ≤ P.randLen)
    (fit : 96 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ P.g.W.toNat ∨ P.g.W.toNat + P.g.L + 96 ≤ (s.gpr .esp).toNat)
    (randPrivateFar : (⟨P.rand.setWidth 64, P.randLen⟩ : Region).Disjoint (below (s.gpr .esp) 28)) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateTest.code P.g.w montName mont roundName round) s fun t =>
      val32 t.mem P.g.W (P.g.array 0) P.g.words = P.candidate ∧ MillerRabinLoop.Result P t ∧
      WorkspaceFrame P.g (ranges P.g) s.mem t.mem ∧
      Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 96] s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateTest.code
  refine CandidateFrame.code_full_ok (CandidateNoSp.core montNoSp roundNoSp P.g.w montName roundName) S v.geometry.headerFit capacity fit separate ?_
  intro a Sa Ca _ Fa Ka
  have workspaceFar : (⟨P.g.W, P.g.L⟩ : Region).Disjoint (below (s.gpr .esp) 28) :=
    FilterStack.allocated_apart (by omega) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))
  have Wa : WorkspaceFrame P.g [] s.mem a.mem := by
    intro i index _
    exact Fa.bytes (R := ⟨P.g.W, P.g.L⟩)
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
      (by change P.g.L ≤ 2 ^ 64; have := S.nowrap; omega) index
  have I : Prepare.Input P.g P.candidate P.capacity P.p a := by
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
  have outerFrame : Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 96] s.mem t.mem := by
    have first : Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 96] s.mem a.mem :=
      Fa.sub (by
        intro r mem; obtain rfl := List.mem_singleton.mp mem
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), below_sub (by decide) fit⟩)
    have second : Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 96] a.mem t.mem :=
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
