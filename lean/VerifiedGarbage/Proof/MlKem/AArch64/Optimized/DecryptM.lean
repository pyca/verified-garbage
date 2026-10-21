module
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptW
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.VRest
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Ops
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Lists
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemUContext
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReady
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Complete decryption with 16-bit coefficients and a single fused secret-vector dot product -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}

theorem fused_m_ok {s₀ s : State} (hp : Pre P (deL P) s₀) (hc : Calls P) (htr : Optimized.TransformTables s) (h : DInv P s₀ 0 s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint ⟨kA s₀ (deL P).sc,P.scl⟩) :
    WP isa (Impl.MlKem.AArch64.Optimized.decryptM P) s fun t => KB P (deL P) s₀ t ∧ t.gpr .x24=1 ∧
      bytesAt t.mem (sA (deL P) s₀ MB) 32=mD P s₀ := by
  have hw := hp.wf
  have far : ∀o l, o+l≤P.scl → (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint
      (R (kA s₀) (deL P).sc o l) := by
    intro o l hf
    have hd : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) (deL P).sc 0 P.scl) := by
      simpa only [R,ptr_zero] using ha
    exact hd.sub_right (R.sub2 (by omega) (by omega))
  apply WPs.seqs (by simp)
  rw [List.append_assoc]
  apply WPs.append
  refine WPs.mono_syms (uW_all hp hc htr ⟨h.kb,h.x24,fun _ hj => by omega⟩) fun t ⟨dt,ft,trt⟩ hs => ?_
  have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [hs]; apply gamma_frame ht ft
    intro r hh
    simp only [uWritesW, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl <;> exact far _ _ (by lom)
  have hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ ((deL P).slot 0)+BitVec.ofNat 64 (0+384*j)) 384)=
      dcS (KPke.dkPke P.params (dkD P s₀)) j := by
    intro j hj
    simp only [deL,Nat.zero_add]
    rw [←bytesAt_slice s₀.mem (kA s₀ 0) (show 384*j+384≤(deL P).len 0 by dek),dcS_eq s₀ hj]
    rfl
  have d0 : DecodeInvW P (deL P) s₀ t.mem (dcS (KPke.dkPke P.params (dkD P s₀)))
      (fun j => ntt (KPke.dcU P.params (cD P s₀) j)) 1 0 t :=
    ⟨dt.kb,dt.x24,fun _ hj => by omega,dt.u,Frame.refl _ _⟩
  apply WPs.append
  have dec := WPs.range (fun _ hj _ h => decode_stepW hp (kE := 0) (eo := 0) (by decide) (by change 0<2; decide)
    (by dek) hj hT h) d0
  simp only [Nat.zero_add] at dec
  refine WPs.mono_syms dec fun u du hsu => ?_
  have gu : Dot.GammaArtifact u.mem (u.syms "VG_MLKEM_GAMMA") := by
    rw [hsu]
    apply gamma_frame gt du.frame
    intro r hh
    rw [List.mem_singleton.mp hh,hs]
    have hkk := Nat.mul_le_mul_right P.k hw.facts.1
    simp only [Nat.one_mul] at hkk
    exact far _ _ (by lom)
  have cu : Covers [⟨u.syms "VG_MLKEM_GAMMA",512⟩] (u.rd++u.wr) := by
    simpa only [hsu,hs,du.kb.rd,du.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
  have au : (polyRegion (sA (deL P) s₀ (TP P))).Disjoint ⟨u.syms "VG_MLKEM_GAMMA",512⟩ := by
    rw [hsu,hs]; exact (far _ _ (by lom)).symm
  have tru := trt.frame hsu (du.kb.rd.trans dt.kb.rd.symm) (du.kb.wr.trans dt.kb.wr.symm)
    (du.kb.sp.trans dt.kb.sp.symm) du.frame (cov_w hp dt.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  refine WPs.cons (WP.mono_syms (fusedW_ok hp (po_TP hw) du.kb (decodedTerms P)
    (decoded_readyW hp du gu cu au).data) fun w ⟨kw,fw,pw,xw⟩ hus => ?_)
  rw [decoded_sum] at pw
  have trw := tru.frame hus (kw.rd.trans du.kb.rd.symm) (kw.wr.trans du.kb.wr.symm)
    (kw.sp.trans du.kb.sp.symm) fw (cov_w hp du.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  exact m_tailW hp hc trw kw (xw.trans du.x24) pw

end VG.Proof.MlKem.AArch64.Decaps
