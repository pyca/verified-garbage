module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeParametersCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Generate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeParameters
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash

/-! # Complete search and output timing for each supported parameter size -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation

def ParameterPublic.output (p : ParameterPublic) : OutputPublic :=
  ⟨p.context, (p.context.remaining 0 p.randUsed).isSome, p.ws⟩

theorem nativeParameters_output (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    {n pLen qLen : Nat} {p : ParameterPublic} {s : State} (h : ParameterStart n pLen qLen p s) :
    WP isa (parameterSearch H.sha1 H.sha256 Sq.mm M.mm K.run pLen qLen) s (OutputBefore n p.output) := by
  obtain ⟨⟨W, hm, h16⟩, hf, _, hp, hq⟩ := h
  subst pLen; subst qLen
  refine WP.mono (nativeParameters_ok H M Sq K hm h16 p.randBound)
    fun t ⟨Wt, ht, outcome, _, _, wr⟩ => ?_
  refine ⟨⟨Wt, ht, ?_⟩, hf.congr (ht.layout.rsp.trans hm.layout.rsp.symm) wr⟩
  change (Wt 19 == 1) = (p.context.remaining 0 p.randUsed).isSome
  rcases outcome with ⟨h19, he⟩ | ⟨h19, a, he, _⟩
  · rcases h19 with hs | hs <;> simp [hs, he]
  · simp [h19, he]

theorem generate_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterStart n pLen qLen))
      (generate H.sha1 H.sha256 Sq.mm M.mm K.run pLen qLen) (fun _ _ => True) := by
  refine RelCT.seq (two_post (nativeParameters_ct H M Sq K n hn pLen qLen sizes)
    (fun _ _ h => nativeParameters_output H M Sq K h)) ?_
  exact two_map ParameterPublic.output (fun _ _ h => h) (finishOutput_ct n hn)

end VG.Proof.Dsa.X86_64.Generation
