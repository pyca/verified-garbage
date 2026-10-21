module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Noise
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.VRest
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Noise
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.URow
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemUContext
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.VRest
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.URow

/-! # The 16-bit encryption after the matrix computed PRF outputs

`encrypt_restP`: `Kem16P.encryptRestP`, the noise from the buffers
(`noiseP_ok`), then the rows of `u` and `v` (`after_noiseP`), as
`Kem.encrypt_restW`. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem16P
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem
variable {P : KemLay} {L : Layout}
variable {prf : Nat→Nat→Prog isa}

/-- The rows of `u` and `v`, `e₂` at `EP` already if `e2`. -/
theorem after_noiseP (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) (e2 : Bool)
    {mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co s.mem mB v rv mv P.k 0 s) (he : ErrorsW P L s₀ rv s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hE : e2 = true → PolyIsW 16 s.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k))) :
    WP isa (seqs (((List.range P.k).map (Kem16.uRow P (slotReg kC) co)) ++
      [Impl.MlKem.AArch64.Kem16P.vRestP prf P e2 (slotReg kE) eo .x28 MB (slotReg kC) co])) s
      (fun t => VInvW P L s₀ kC co s.mem mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  apply WPs.seqs (by simp)
  apply WPs.append
  cases e2
  · refine WPs.mono (u_rowsW hp hr hc A htr h he ht hcT ha) fun t ⟨et,hs⟩ => ?_
    have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht et.fr ha
    have ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,et.kb.rd,et.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    exact WPs.single (v_restP valid hp hc A false hT (transform_enc_frame hp A h.kb et.kb htr hs et.fr)
      et.vinv gt ct (by simpa only [hs] using ha) (fun h => absurd h (by decide)))
  · refine WPs.mono (u_rowsE hp hr hc A htr h he ht hcT ha (hE rfl)) fun t ⟨et,hs,qt⟩ => ?_
    have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht et.fr ha
    have ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,et.kb.rd,et.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    exact WPs.single (v_restP valid hp hc A true hT (transform_enc_frame hp A h.kb et.kb htr hs et.fr)
      et.vinv gt ct (by simpa only [hs] using ha) (fun _ => qt))

/-- What the noise writes, `scratch` may be written. -/
theorem noiseW_cov {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (h : KB P L s₀ s) :
    Covers (noiseW P L s₀) s.wr := by
  have hw := hp.wf
  refine Covers.cons (cov_s hp h (by lom)) (Covers.cons (cov_s hp h (by lom)) (Covers.cons ?_ Covers.nil))
  refine cov_w hp h ⟨hp.scw, hp.scb⟩ ?_
  rw [hp.scl]; have := Noise.noise_fits (P := P) hr (i := P.k - 1) (by have := hw.facts; omega)
  simp only [Impl.MlKem.AArch64.Noise.noiseOff] at this ⊢; have := hw.facts; omega

/-- **The noise, `u` and `v`**, the first `n ≥ 2k` PRF outputs in their buffers. -/
theorem encrypt_restP (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {n : Nat} (hn : 2 * P.k ≤ n)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co mE mB v rv mv 0 0 s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn' : ∀r∈noiseW P L s₀, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hprf : ∀ N < min n (Impl.MlKem.AArch64.Kem16P.prfs P), PrfAt P L s₀ s.mem s.mem N) :
    WP isa (Impl.MlKem.AArch64.Kem16P.encryptRestP prf P n (slotReg kE) eo .x28 MB (slotReg kC) co) s
      (fun t => ∃mN, Frame (noiseW P L s₀) s.mem mN ∧
        VInvW P L s₀ kC co mN mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  have hk := hw.facts
  refine WP.seq (WP.mono (noiseP_ok (prf := prf) hp hr h.kb htr hn h.r hprf) fun t nt => ?_)
  have hcnt : 2 * P.k ≤ min n (Impl.MlKem.AArch64.Kem16P.prfs P) := by
    simp only [Impl.MlKem.AArch64.Kem16P.prfs]; omega
  have far : ∀ {o l : Nat}, o + l ≤ SV P + 48 →
      (o + l ≤ NS ∨ (NS + 1024 ≤ o ∧ o + l ≤ YH P) ∨ TP P ≤ o) →
      ∀ r ∈ noiseW P L s₀, (R (kA s₀) L.sc o l).Disjoint r := fun hf ho => noiseW_far hp hr hf ho
  have e0 : EInvW true P L s₀ kC co t.mem mB v rv mv P.k 0 t := by
    refine ⟨nt.kb, nt.x24.trans h.x24, ?_, ?_, fun i hi j hj => ?_, fun j hj => ?_,
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
    · rw [bytesAt_frame nt.fr (far (o := RB) (l := 32) (by lom) (.inl (by lom))) (by decide)]; exact h.r
    · rw [bytesAt_frame nt.fr (far (o := MB) (l := 32) (by lom) (.inl (by lom))) (by decide)]; exact h.m
    · have := ij_lt hi hj
      have fa := far (o := aOff P i j) (l := 1024) (by lom) (.inr (.inl ⟨by lom, by lom⟩))
      exact ⟨reducedW_frame nt.fr fa (h.a i hi j hj).1, (polyAtW_frame nt.fr fa).trans (h.a i hi j hj).2⟩
    · have d := nt.done j (by omega)
      simp only [Impl.MlKem.AArch64.Kem16P.target, tPoly, ite_eq_left hj] at d
      exact d
  have er : ErrorsW P L s₀ rv t := by
    intro j hj
    have d := nt.done (P.k + j) (by omega)
    simp only [Impl.MlKem.AArch64.Kem16P.target, tPoly, ite_eq_right (show ¬ P.k + j < P.k by omega),
      ite_eq_left (show P.k + j < 2 * P.k by omega), Nat.add_sub_cancel_left] at d
    exact d
  have hE : decide (Impl.MlKem.AArch64.Kem16P.prfs P ≤ n) = true →
      PolyIsW 16 t.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) := by
    intro he
    have he' : Impl.MlKem.AArch64.Kem16P.prfs P ≤ n := of_decide_eq_true he
    have d := nt.done (2 * P.k) (by simp only [Impl.MlKem.AArch64.Kem16P.prfs] at he' ⊢; omega)
    simp only [Impl.MlKem.AArch64.Kem16P.target, tPoly, ite_eq_right (show ¬ 2 * P.k < P.k by omega),
      Nat.lt_irrefl, ite_false] at d
    exact d
  have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [nt.syms]; exact gamma_frame ht nt.fr hn'
  have ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
    simpa only [nt.syms, nt.kb.rd, nt.kb.wr, ← h.kb.rd, ← h.kb.wr] using hcT
  have tt := htr.frame nt.syms (nt.kb.rd.trans h.kb.rd.symm) (nt.kb.wr.trans h.kb.wr.symm)
    (nt.kb.sp.trans h.kb.sp.symm) nt.fr (noiseW_cov hp hr h.kb)
  exact WP.mono (after_noiseP valid hp hr hc A _ hT tt e0 er gt ct (by simpa only [nt.syms] using ha) hE)
    fun u ⟨eu, vu⟩ => ⟨t.mem, nt.fr, eu, vu⟩

end VG.Proof.MlKem.AArch64.Kem16P
