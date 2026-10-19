module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenFinish
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutTables
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenNoise

/-! # Paired noise preserves key-generation inputs and caller state -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay}

theorem readonly_noise_encode {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (ht : Optimized.TransformTables s)
    {mB : Mem} {v : BitVec 64} (h : CInv P s₀ mB v s) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWith P true) s fun t =>
      Kept (Noise.allWrites P true (kA s₀ 3)) s t ∧ EncodeInv P s₀ mB t.mem v 0 t := by
  have hc : Covers [⟨kA s₀ 3,P.scl⟩] s.wr := by
    have hh := cov_w hp h.kb (b := 3) (o := 0) (l := P.scl) (by decide) (by kl)
    simpa only [R,ptr_zero] using hh
  refine WP.mono (Noise.readonly_noiseAll_tables hp.wf hr true h.kb.x28 hc ht) fun t ⟨kt,pt⟩ => ?_
  refine ⟨kt,noise_cinv hp hr h kt,?_,?_,fun _ hj => by omega,Frame.refl _ _⟩
  · intro j hj
    have p : PolyIs _ _ _ := pt j (by omega)
    simpa only [Noise.outOff,ite_eq_left hj,ite_true,Noise.sampled,Noise.seedOff,Noise.transformed,
      Bool.true_or,h.sig,KPke.kgS,cbd] using p
  · intro j hj
    have p : PolyIs _ _ _ := pt (P.k+j) (by omega)
    have hn : ¬P.k+j<P.k := by omega
    simpa only [Noise.outOff,ite_eq_right hn,Nat.add_sub_cancel_left,Noise.sampled,Noise.seedOff,
      Noise.transformed,Bool.true_or,ite_true,h.sig,KPke.kgE,cbd,KemLay.params] using p

end VG.Proof.MlKem.AArch64.KeyGen
