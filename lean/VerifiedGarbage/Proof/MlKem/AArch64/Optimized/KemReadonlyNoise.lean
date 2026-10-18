module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutTables
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise

/-! # Paired encryption noise preserves read inputs and caller state -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

theorem readonly_noise_einv {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (ht : Optimized.TransformTables s)
    {kC co : Nat} {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte}
    (h : EInv P L s₀ kC co mE mB v rv mv 0 0 s) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWith P false) s fun t =>
      Kept (Noise.allWrites P false (kA s₀ L.sc)) s t ∧
      EInv P L s₀ kC co t.mem mB v rv mv P.k 0 t ∧ Errors P L s₀ rv t := by
  have hw := hp.wf
  have hroom := hr.kem
  have hc : Covers [⟨kA s₀ L.sc,P.scl⟩] s.wr := by
    have hh := cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o := 0) (l := P.scl) (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.mono (Noise.readonly_noiseAll_tables hw hr false h.kb.x28 hc ht) fun t ⟨kt,pt⟩ => ?_
  have keepB : ∀o l, o+l≤SS → o+l≤P.scl-1024*P.k →
      (Spec.Sha3.bytesAt t.mem (sA L s₀ o) l=Spec.Sha3.bytesAt s.mem (sA L s₀ o) l) := by
    intro o l ho ht
    exact bytesAt_frame kt.frame (noise_far hp hr hp.scb (hp.fs (by lom)) (.inr (by lom))) (by lom)
  refine ⟨kt,⟨noise_kb hp hr h.kb kt,(kt.cs .x24 (by decide) (by decide)).trans h.x24,
    (keepB RB 32 (by decide) (by lom)).trans h.r,
    (keepB MB 32 (by decide) (by lom)).trans h.m,?_,?_,fun _ hj => by omega,Frame.refl _ _⟩,?_⟩
  · intro i hi j hj
    have hij := ij_lt hi hj
    have far := noise_far hp hr hp.scb (hp.fs (by lom : aOff P i j+1024≤SV P+48))
      (.inr (by lom))
    exact ⟨reduced_frame kt.frame far (h.a i hi j hj).1,
      (polyAt_frame kt.frame far).trans (h.a i hi j hj).2⟩
  · intro j hj
    have p := pt j (by omega)
    show PolyIs t.mem (sA L s₀ (yOff P j)) _
    simpa only [Noise.outOff,ite_eq_left hj,Bool.false_eq_true,ite_false,Noise.sampled,Noise.seedOff,
      Noise.transformed,decide_eq_true_eq.mpr hj,Bool.false_or,ite_true,h.r,encY,cbd] using p
  · intro j hj
    have p := pt (P.k+j) (by omega)
    have hn : ¬P.k+j<P.k := by omega
    simpa only [Noise.outOff,ite_eq_right hn,Nat.add_sub_cancel_left,Noise.sampled,Noise.seedOff,
      Noise.transformed,decide_eq_false_iff_not.mpr hn,Bool.false_or,Bool.false_eq_true,ite_false,h.r,cbd] using p

end VG.Proof.MlKem.AArch64.Kem
