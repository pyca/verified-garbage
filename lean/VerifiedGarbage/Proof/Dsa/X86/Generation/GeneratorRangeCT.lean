module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTestFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleHeadCT

/-! # Generator range classification depends on the public h candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem generatorRange_ct (G : PrimeConfig) :
    RelCT isa (Two (GeneratorCandidateAt G)) (sampleHead G.len) (Two (GeneratorRangeAt G)) := by
  refine two_post ((sampleHead_ct G.len).mono ?_ (fun _ _ h => h)) ?_
  · rintro s t ⟨p, hs, ht⟩ r hr
    obtain ⟨Ws, Rs⟩ := hs.resources
    obtain ⟨Wt, Rt⟩ := ht.resources
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (Rs.ready.context.scr.edi_toNat.trans Rt.ready.context.scr.edi_toNat.symm)
    · exact hs.pointer.trans ht.pointer.symm
  · intro p s H
    obtain ⟨W, R⟩ := H.resources
    refine WP.mono (generatorRange_ready R.ready
      (by rw [H.pointer]; exact H.fit)
      (fun d hd => by rw [H.pointer]; exact H.read d hd)
      (by rw [H.pointer]; exact H.apart)) fun t ⟨Rt, value, zf, O, K⟩ => ?_
    rw [H.pointer, H.value] at value zf
    refine ⟨H.layout, ⟨W, Rt, R.searchFrame.keeps K (by decide), R.representation.keep O.testFrame H.layout.frameApart,
      R.savedParent, ?_, ?_⟩, value, ?_, zf⟩
    · intro d hd; rw [K.2.1, K.2.2]; exact R.exponentRead d hd
    · intro d k hd; rw [K.2.2]; exact R.outputWrite d k hd
    · rw [drawFrame_bytes O.testFrame H.layout.exponentApart (by have := G.lenMax; omega)]
      exact H.exponent
end VG.Proof.Dsa.X86.Generation
