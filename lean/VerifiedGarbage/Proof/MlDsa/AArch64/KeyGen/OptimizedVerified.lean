import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSat

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts signRootConsts_eq)

theorem keyGen_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params}
    (hp : p=mlDsa44∨p=mlDsa65∨p=mlDsa87) :
    Verified target (keyGenWith v.callee p) (keyGenContract p (abi.withConsts signRootConsts) 16) := by
  have hF := pfacts hp
  have hm : p.k*p.ℓ%4=0∨p.k*p.ℓ%4=2 := by rcases hp with rfl|rfl|rfl <;> decide
  have hs : (p.ℓ+p.k)%4=0∨(p.ℓ+p.k)%4=3 := by rcases hp with rfl|rfl|rfl <;> decide
  have hP := primitives_ok (keccak := v)
  have hdpre : 16*(prefixWith v.callee (primitives v.callee)
      Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code p).aarch64Depth≤16 := by
    have h := (prefix_dle v hF).le; omega
  have hdpack : ∀j<p.ℓ+p.k,16*(packSecret (primitives v.callee) p j).aarch64Depth≤16 := by
    intro j _; have h := (packSecret_dle v p j).le; omega
  have hdrow : ∀i<p.k,16*(row (primitives v.callee) p i).aarch64Depth≤16 := by
    intro i _; have h := (row_dle v hp i).le; omega
  refine ⟨?_,?_,⟨keyGenSat p,keyGen_sat hp⟩⟩
  · intro s h
    obtain ⟨pre,roots⟩ := staticRoots_entry (by decide) h
    exact codeWith_ok hP two_callee hF hm hs pre roots hdpre hdpack hdrow
  · intro s t tr ur s' t' hσ hτ pub es et
    have preσ := staticRoots_entry (by decide) hσ
    have preτ := staticRoots_entry (by decide) hτ
    have pb : kgPub p 16 s t ∧ TableEq s t := by
      sig_pub [keyGenContract,keyGenSig,abi,argRegs,Abi.withConsts,signRootConsts_eq] at pub
      obtain ⟨hsp,hf,hi,hb,h0,h1,h2,h3⟩ := pub
      refine ⟨?_,hf,hi⟩
      dsimp only [kgPub]
      sig_pub [keyGenContract,keyGenSig,abi,argRegs]
      exact ⟨hsp,hb,h0,h1,h2,h3⟩
    exact codeWith_ct hP two_callee hF hm hs hdpre hdpack hdrow
      s t tr ur s' t' preσ preτ pb es et

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
