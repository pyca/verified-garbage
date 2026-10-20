module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorCTState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorOutputCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorEvaluateCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReadyMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTestFrame

/-! # Evaluate an in-range generator and publish its public success status -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def generatorEvaluatePublic (G : PrimeConfig) (p : GeneratorCandidatePublic) : GeneratorEvaluatePublic :=
  ⟨p.power G, generatorExponentPointer (p.frame.words 5)⟩

def GeneratorExponentAt (G : PrimeConfig) (p : GeneratorCandidatePublic) (s : State) : Prop :=
  GeneratorEvaluateAt G.len (generatorEvaluatePublic G p) s ∧ GeneratorFrameAt G p s ∧
    GeneratorLayout G p.frame.base (p.frame.words 5)

def generatorOutputPublic (G : PrimeConfig) (p : GeneratorCandidatePublic) : GeneratorOutputPublic :=
  ⟨p.frame, G.base.setWidth 32, if 1 < (p.power G).result then 1 else 3⟩

theorem generatorExponentArgs_ct (G : PrimeConfig) : RelCT isa (Two (GeneratorRangeAt G))
    (.block (bufferPointer .esi VG.Impl.Dsa.Generation.Layout.exponent)) (Two (GeneratorExponentAt G)) := by
  refine two_piece [.esp] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨Ws, Rs⟩ := hs.resources
    obtain ⟨Wt, Rt⟩ := ht.resources
    exact BitVec.eq_of_toNat_eq (Rs.searchFrame.esp_toNat.trans Rt.searchFrame.esp_toNat.symm)
  · intro p s H
    obtain ⟨W, R⟩ := H.resources
    refine WP.mono (bufferPointer_ok R.searchFrame ((R.representation 5 (by decide)).trans R.savedParent) .esi _)
      fun t ⟨si, mem, K⟩ => ?_
    have Rt := R.ready.frame (by rw [mem]; exact Frame.refl [] s.mem) (by simp) K (by decide) (by decide)
    refine ⟨⟨Rt.context, G.width, G.lenWords, Rt.one, Rt.r2, ?_, ?_, si, H.layout.exponentFit, ?_, H.layout.exponentScratch⟩,
      ⟨W, Rt, R.searchFrame.keeps K (by decide), ?_, R.savedParent, ?_, ?_⟩, H.layout⟩
    · rw [mem]; exact H.value
    · rw [mem]; exact H.exponent
    · intro d hd; rw [K.2.1, K.2.2]; exact R.exponentRead d hd
    · rw [mem]; exact R.representation
    · intro d hd; rw [K.2.1, K.2.2]; exact R.exponentRead d hd
    · intro d k hd; rw [K.2.2]; exact R.outputWrite d k hd

theorem generatorEvaluated_ct (G : PrimeConfig) : RelCT isa (Two (GeneratorExponentAt G))
    (generatorEvaluate G.len)
    (Two fun p s => GeneratorStoreAt (generatorOutputPublic G p) s ∧
      s.gpr .eax = (generatorOutputPublic G p).status) := by
  refine two_post (two_map (generatorEvaluatePublic G) (fun _ _ h => h.1) (generatorEvaluate_ct G.len G.lenMin)) ?_
  · intro p s H
    obtain ⟨W, R⟩ := H.2.1
    refine WP.mono (generatorEvaluate_ready R.ready
      (by rw [H.1.pointer]; exact H.1.fit)
      (fun d hd => by rw [H.1.pointer]; exact H.1.read d hd)
      (by rw [H.1.pointer]; exact H.1.apart)) fun t ⟨Rt, _, status, O, K⟩ => ?_
    have Wt := R.representation.keep O.testFrame H.2.2.frameApart
    refine ⟨⟨⟨R.searchFrame.keeps K (by decide), ?_⟩, ?_⟩, ?_⟩
    · intro i hi
      obtain rfl := List.mem_singleton.mp hi
      exact (Wt 5 (by decide)).trans R.savedParent
    · change t.gpr .edi = G.base.setWidth 32
      rw [← Rt.context.scr.edi]
      simp
    · rw [H.1.pointer, H.1.exponent] at status
      have value : wordsVal s.mem G.base (slot G.n 5) G.n = p.value := H.1.value
      rw [value] at status
      exact status

theorem generatorAccepted_ct (G : PrimeConfig) : RelCT isa (Two (GeneratorRangeAt G))
    (.seq (.block (bufferPointer .esi VG.Impl.Dsa.Generation.Layout.exponent))
      (.seq (generatorEvaluate G.len)
        (.seq (.block [.store (frameSlot 19) .eax]) (onSuccess (generatorStore G.len))))) (fun _ _ => True) := by
  refine RelCT.seq (generatorExponentArgs_ct G) (RelCT.seq (generatorEvaluated_ct G) ?_)
  exact two_map (generatorOutputPublic G) (fun _ _ h => h) (generatorOutput_ct G.len)
end VG.Proof.Dsa.X86.Generation
