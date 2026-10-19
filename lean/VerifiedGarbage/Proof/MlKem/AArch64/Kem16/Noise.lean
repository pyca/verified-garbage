module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyNoise
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Ops

/-! # The 16-bit encryption noise

`readonly_noise_einv` for the noise of `Kem16.encryptRest`, stored with 16 bits:
`ŷ` into `YH`, and `e₁` and `e₂` past the KEM's buffers (`ErrorsW`). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

/-- `e₁` and `e₂`, stored with 16 bits past the KEM's buffers. -/
def ErrorsW (P : KemLay) (L : Layout) (s₀ : State) (rv : List Byte) (s : State) : Prop :=
  ∀j<P.k, PolyIsW 16 s.mem (sA L s₀ (Impl.MlKem.AArch64.Noise.noiseOff P j)) (cbd rv (P.k+j))

theorem noiseW_einv {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (ht : Optimized.TransformTables s)
    {kC co : Nat} {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte}
    (h : EInvW true P L s₀ kC co mE mB v rv mv 0 0 s) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWithW P false true) s fun t =>
      Kept (Noise.allWrites P false (kA s₀ L.sc)) s t ∧
      EInvW true P L s₀ kC co t.mem mB v rv mv P.k 0 t ∧ ErrorsW P L s₀ rv t := by
  have hw := hp.wf
  have hroom := hr.kem
  have hc : Covers [⟨kA s₀ L.sc,P.scl⟩] s.wr := by
    have hh := cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o := 0) (l := P.scl) (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.mono (Noise.readonly_noiseAll_tables (w16 := true) hw hr false h.kb.x28 hc ht) fun t ⟨kt,pt⟩ => ?_
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
    exact ⟨reducedW_frame kt.frame far (h.a i hi j hj).1,
      (polyAtW_frame kt.frame far).trans (h.a i hi j hj).2⟩
  · intro j hj
    have p : PolyIsW 16 _ _ _ := pt j (by omega)
    show PolyIsW 16 t.mem (sA L s₀ (yOff P j)) _
    simpa only [Noise.outOff,ite_eq_left hj,Bool.false_eq_true,ite_false,Noise.sampled,Noise.seedOff,
      Noise.transformed,decide_eq_true_eq.mpr hj,Bool.false_or,ite_true,h.r,encY,cbd] using p
  · intro j hj
    have p : PolyIsW 16 _ _ _ := pt (P.k+j) (by omega)
    have hn : ¬P.k+j<P.k := by omega
    simpa only [Noise.outOff,ite_eq_right hn,Nat.add_sub_cancel_left,Noise.sampled,Noise.seedOff,
      Noise.transformed,decide_eq_false_iff_not.mpr hn,Bool.false_or,Bool.false_eq_true,ite_false,h.r,cbd] using p

end VG.Proof.MlKem.AArch64.Kem
