module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeParametersCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterInvariant
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Generate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeParameters

/-! # Complete search and output timing for each supported parameter size -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

def ParameterPublic.output (p : ParameterPublic) : OutputPublic :=
  ⟨p.context, (p.context.remaining 0 p.randUsed).isSome⟩

theorem nativeParameters_output (H : GenerationHashes) (G : GeneratorStage)  (T : PrimeTest)
    {pLen qLen : Nat} {p : ParameterPublic} {s : State} (h : ParameterStart pLen qLen p s) :
    WP isa (parameterSearch H.sha1 H.sha256 G.run T.run pLen qLen) s (OutputBefore p.output) := by
  obtain ⟨⟨W, hm, h16⟩, hp, hq⟩ := h
  subst pLen; subst qLen
  refine WP.mono (nativeParameters_ok H G T hm h16 p.randBound)
    fun t ⟨Wt, ht, outcome, _, _, wr⟩ => ?_
  refine ⟨Wt, ht, ?_⟩
  change (Wt 19 == (1#64)) = (p.context.remaining 0 p.randUsed).isSome
  rcases outcome with ⟨h19, he⟩ | ⟨h19, a, he, _⟩
  · rcases h19 with hs | hs <;> simp [hs, he]
  · simp [h19, he]

theorem generate_ct (H : GenerationHashes) (G : GeneratorStage)  (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterStart pLen qLen))
      (generate H.sha1 H.sha256 G.run T.run pLen qLen) (fun _ _ => True) := by
  refine RelCT.seq (two_post (nativeParameters_ct H G T pLen qLen sizes)
    (fun _ _ h => nativeParameters_output H G T h)) ?_
  exact two_map ParameterPublic.output (fun _ _ h => h) finishOutput_ct

end VG.Proof.Dsa.AArch64.Generation
