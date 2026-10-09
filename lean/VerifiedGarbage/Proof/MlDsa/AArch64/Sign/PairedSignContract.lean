import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedSignSat
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- Internal signing contract: the original outcome and leakage, with immutable roots. -/
def pairedSignK (p : Params) (S : Nat) : Contract isa where
  pre s := (signK p S).pre s ∧ StaticRoots S s ∧ PairedRoots S s
  post := (signK p S).post
  pub s t := (signK p S).pub s t ∧ RootSymbolsEq s t ∧ s.syms "VG_MLDSA_INV_PAIR"=t.syms "VG_MLDSA_INV_PAIR"

theorem pairedSignK_implies {p : Params} (hp : Ok3 p) :
    (pairedSignK p signStack).Implies
      (signContractT p (abi.withConsts pairedSignRootConsts) signStack) where
  pre := by
    intro s h
    exact pairedRoots_entry (by decide) h
  post := by
    sig_implies_post [signContractT, signSig, pairedSignK, signK, abi, argRegs,
      Abi.withConsts]
  pub := by
    intro s t _ _ h
    sig_pub [signContractT,signSig,abi,argRegs,Abi.withConsts,pairedSignRootConsts_eq] at h
    obtain ⟨hsp,hf,hi,hp,hb,h0,h1,h2,h3,h4⟩ := h
    exact ⟨⟨h0,h1,h2,h3,h4,hsp,hb⟩,⟨hf,hi⟩,hp⟩
  sat := ⟨pairedSignSat p,pairedSign_sat hp⟩

theorem pairedSignK_implies_spec {p : Params} (hp : Ok3 p) :
    (pairedSignK p signStack).Implies
      (signContract p (abi.withConsts pairedSignRootConsts) signStack) := by
  rw [← signContractT_eq]
  exact pairedSignK_implies hp

end VG.Proof.MlDsa.AArch64.Sign
