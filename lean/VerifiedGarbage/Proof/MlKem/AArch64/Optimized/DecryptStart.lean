module

import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptSeed
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptM
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemUContext
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Decapsulation prologue and seed derivation with fused decryption -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
variable {P : KemLay}
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem start_using_ok (hash : FixedHash.HashFn)
    (hash_ok : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x28,MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KP,32⟩,⟨.x28,RB,32⟩])
    {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) (htr : Optimized.TransformTables s₀)
    (ht : Dot.GammaArtifact s₀.mem (s₀.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s₀.syms "VG_MLKEM_GAMMA",512⟩] (s₀.rd++s₀.wr))
    (ha : (⟨s₀.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint ⟨kA s₀ (deL P).sc,P.scl⟩) :
    WP isa (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P) s₀ (AfterA P s₀) := by
  have hw := hp.wf
  refine WP.seq (WP.mono_syms (prologue_ok hp) fun s₁ h₁ hs => ?_)
  have gt : Dot.GammaArtifact s₁.mem (s₁.syms "VG_MLKEM_GAMMA") := by
    rw [hs]
    rcases h₁.mem with hm | hf
    · rwa [hm]
    · apply gamma_frame ht hf
      intro r hh
      rw [List.mem_singleton.mp hh]
      exact ha.sub_right (R.sub (by lom))
  have ct : Covers [⟨s₁.syms "VG_MLKEM_GAMMA",512⟩] (s₁.rd++s₁.wr) := by
    simpa only [hs,h₁.keep.rd,h₁.keep.wr] using hcT
  have tr₁ : Optimized.TransformTables s₁ := by
    apply htr.frame hs h₁.keep.rd h₁.keep.wr h₁.keep.sp
    · rcases h₁.mem with hm | hf
      · simpa only [hm] using Frame.refl [R (kA s₀) (deL P).sc (SV P) 48] s₀.mem
      · exact hf
    · exact cov_w₀ hp ⟨hp.scw,hp.scb⟩ (hp.fs (by omega))
  refine WP.seq (WP.mono (fused_m_ok hp hc tr₁ ⟨h₁.kb,h₁.x24,fun _ hj => by omega⟩ gt ct
    (by simpa only [hs] using ha)) fun s₂ ⟨kb₂,x₂,m₂⟩ => ?_)
  exact a_tail_using hash hash_ok hp kb₂ x₂ m₂

theorem start_ok {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) (htr : Optimized.TransformTables s₀)
    (ht : Dot.GammaArtifact s₀.mem (s₀.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s₀.syms "VG_MLKEM_GAMMA",512⟩] (s₀.rd++s₀.wr))
    (ha : (⟨s₀.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint ⟨kA s₀ (deL P).sc,P.scl⟩) :
    WP isa (Impl.MlKem.AArch64.Optimized.deStart keccak.callee P) s₀ (AfterA P s₀) :=
  start_using_ok _ (FixedHash.hashWith_correct keccak _ _ _ _ _ _ _) hp hc htr ht hcT ha

end VG.Proof.MlKem.AArch64.Decaps
