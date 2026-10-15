module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReady
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemAdd
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyTransform
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # One fused ciphertext row using retained noise -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay} {L : Layout}

theorem readonly_fused_u_row {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInv P L s₀ kC co mE mB v rv mv P.k i s)
    {F G : (Nat × Nat) → Poly}
    (hd : Dot.LoopData s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (uTerms P i) (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues)
    (hsum : Dot.polySum (uTerms P i) F G = KPke.dotK (fun j => aM P L s₀ mB j i) (encY rv) P.k)
    (ht : Optimized.TransformTables s)
    (he : PolyIs s.mem (sA L s₀ (noiseOff P i)) (cbd rv (P.k+i))) :
    WP isa (seqs [Impl.MlKem.AArch64.Dot.dot (TP P) (uTerms P i),Ntt16.Readonly.nttInvAt (TP P),
      addAt (TP P) (noiseOff P i),P.ceLAt (TP P) P.du (slotReg kC) (co+32*P.du*i)]) s
      (EInv P L s₀ kC co mE mB v rv mv P.k (i+1)) := by
  have hw := hp.wf
  have hn : i≤P.k := Nat.le_of_lt hi
  have ef : noiseOff P i+1024≤L.len L.sc := by rw [hp.scl]; exact Noise.noise_fits hr hi
  have ep := Noise.noise_past_kem hr i
  have far : ∀r∈[R (kA s₀) L.sc (TP P) 1024,R (kA s₀) L.sc NS 1024],
      (polyRegion (sA L s₀ (noiseOff P i))).Disjoint r := by
    intro r hh
    rcases mem2' hh with rfl | rfl <;>
      exact hp.args.rdisj hp.scb hp.scb ef (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  refine WP.seq (WP.mono_syms (fused_einv hp A hn h (uTerms P i) hd) fun s₁ ⟨e₁,f₁,t₁⟩ sy₁ => ?_)
  have p₁ := polyIs_frame f₁ (fun r hh => far r (by rw [List.mem_singleton.mp hh]; exact List.mem_cons_self ..)) he
  rw [hsum] at t₁
  have ht₁ := ht.frame sy₁ (e₁.kb.rd.trans h.kb.rd.symm) (e₁.kb.wr.trans h.kb.wr.symm) (e₁.kb.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=TP P) (l:=1024) (hp.fs (by lom)))
  refine WP.seq (WP.mono (readonly_nttInv_ok hp (po_TP hw) e₁.kb t₁.1 ht₁) fun s₂ ⟨kb₂,f₂,t₂,x₂⟩ => ?_)
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (far_mul hp A (Nat.le_refl _) hn (by lom) (by lom))
  have p₂ := polyIs_frame f₂ far p₁
  rw [t₁.2] at t₂
  refine WP.seq (WP.mono (add_read_ok hp (po_TP hw) (Noise.noise_fits hr hi)
    (.inl (by lom)) e₂.kb t₂.1 p₂.1) fun s₄ ⟨kb₄,f₄,t₄,x₄⟩ => ?_)
  have e₄ := e₂.frame hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₂.2,p₂.2] at t₄
  have fC := A.fC
  have hu := du_le hi
  refine WP.mono (ceL_ok hp hc (off := TP P) (d := P.du) (k := kC) (o := co+32*P.du*i)
    (po_TP hw) (.inl rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom,.inr (by subst hC; lom)⟩)
    e₄.kb t₄.1) fun s₅ ⟨kb₅,f₅,b₅,x₅⟩ => ?_
  have e₅ := e₄.frame hp kb₅ x₅ f₅ fun r hh => by
    rw [List.mem_singleton.mp hh]; exact far_ct hp A (Nat.le_refl _) (by lom)
  refine ⟨e₅.kb,e₅.x24,e₅.r,e₅.m,e₅.a,e₅.y,fun j hj => ?_,e₅.fr⟩
  rcases (by omega : j<i ∨ j=i) with hj | rfl
  · exact e₅.u j hj
  · rw [b₅,t₄.2]; rfl

end VG.Proof.MlKem.AArch64.Kem
