module

import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareMetadata
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Prepare

/-! # Candidate preparation retains every input needed by the blinded loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidatePrepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen

structure Input (P : MillerRabinLoop.Parameters) (s : State) : Prop where
  prepare : Prepare.Input P.g P.candidate P.capacity P.p s P.seed
  readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen
  entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy
  randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand
  randLength : w32 s.mem P.g.W 32 = P.randLen
  used : w32 s.mem P.g.W 152 = P.start

structure Ready (P : MillerRabinLoop.Parameters) (s : State) : Prop where
  prepared : Prepare.Data P.g P.candidate P.capacity P.p s
  readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen
  entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy
  randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand
  randLength : w32 s.mem P.g.W 32 = P.randLen
  used : w32 s.mem P.g.W 152 = P.start

theorem code_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64) {s : State} (I : Input P s) :
    WP isa (VG.Impl.RsaKeyGen.X86.Prepare.codeAt P.seed P.g.w name mont) s fun t =>
      Ready P t ∧ WorkspaceFrame P.g (Prepare.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 80]) s.mem t.mem ∧ Keeps Prepare.clob s t := by
  refine WP.mono (Prepare.code_full_okAt verified noSp stack v.geometry bound v.length I.prepare v.seedPos v.seedLt)
    fun t ⟨T, F, K, W⟩ => ?_
  refine ⟨⟨T, ?_, ?_, ?_, ?_, ?_⟩, W, F, K⟩
  · rw [K.2.1, K.2.2]; exact I.readable
  · rw [frame_bytesAt F (by
      intro r mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with rfl | rfl
      · exact v.randSeparate
      · exact v.randStackFar.sub_right (below_sub (by decide) v.low)) (by have := v.randLenFit; omega)]
    exact I.entropy
  · rw [Prepare.metadata32 v.geometry W (d := 28) (by unfold Prepare.protectedHeader; omega)]
    exact I.randPtr
  · rw [w32, Prepare.metadata32 v.geometry W (d := 32) (by unfold Prepare.protectedHeader; omega)]
    exact I.randLength
  · rw [w32, Prepare.metadata32 v.geometry W (d := 152) (by unfold Prepare.protectedHeader; omega)]
    exact I.used

end VG.Proof.RsaKeyGen.X86.CandidatePrepare
