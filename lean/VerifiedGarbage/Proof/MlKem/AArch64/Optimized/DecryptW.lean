module

public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Ops
import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Decryption with 16-bit coefficients: `û'` and the tail

`uW_all`: each row of `u` decoded and decompressed into `PP`, narrowed to 16 bits at `yOff i`
and transformed by `vg_mlkem16_ntt`. `m_tailW`: after the 16-bit dot product `ŝᵀ ∘ û'`, its
inverse transform, widened into `PP`, subtracted from the decompressed `v` and compressed into
`m'`. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}

/-- After `û'[i]` for `i < n`, stored with 16 bits. -/
structure DInvW (P : KemLay) (s₀ : State) (n : Nat) (s : State) : Prop where
  kb : KB P (deL P) s₀ s
  x24 : s.gpr .x24 = 1
  u : ∀ i < n, PolyIsW 16 s.mem (sA (deL P) s₀ (yOff P i)) (ntt (KPke.dcU P.params (cD P s₀) i))

theorem DInvW.frame {s₀ : State} {n : Nat} {s s' : State} (h : DInvW P s₀ n s) (hk : KB P (deL P) s₀ s')
    (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (kA s₀) (deL P).sc (YH P) (1024 * n)).Disjoint r) : DInvW P s₀ n s' :=
  ⟨hk, by rw [hx, h.x24], fun i hi => polyIsW_frame_poly (w16 := true) hf (fun r hr => (hW r hr).sub_left
    (R.sub2 (by simp only [yOff]; omega) (by simp only [yOff]; omega))) (h.u i hi)⟩

theorem uW_step {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) {i : Nat} (hi : i < P.k) {s : State}
    (ht : Optimized.TransformTables s) (h : DInvW P s₀ i s) :
    WP isa (Impl.MlKem.AArch64.Optimized.deU P i) s fun t => DInvW P s₀ (i + 1) t ∧
      Frame [R (kA s₀) (deL P).sc (PP P) 1024,R (kA s₀) (deL P).sc (yOff P i) 1024,
        R (kA s₀) (deL P).sc NS 1024] s.mem t.mem ∧ Optimized.TransformTables t := by
  have hw := hp.wf
  have hpo := po_y hw hi
  have hu := du_le hi
  have fu : 32 * P.du * i + 32 * P.du ≤ (deL P).len 1 := by dek
  apply WPs.seqs (by simp)
  refine WPs.cons (WP.mono_syms (ddL_ok hp hc (k := 1) (o := 32 * P.du * i) (d := P.du) (off := PP P)
    (by decide) fu (.inl rfl) (po_PP hw) (.inl (by dek)) h.kb) fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ sy₁ => ?_)
  have e₁ := h.frame kb₁ x₁ f₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega) (po_PP hw).le (by lom)
  rw [slice_eq h.kb (b := 1) (by decide) fu] at p₁
  have ht₁ := ht.frame sy₁ (kb₁.rd.trans h.kb.rd.symm) (kb₁.wr.trans h.kb.wr.symm) (kb₁.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=PP P) (l:=1024) (hp.fs (po_PP hw).le))
  refine WPs.cons (WP.mono_syms (narrowW_ok hp (po_PP hw) hpo (by lom) kb₁ p₁)
    fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ sy₂ => ?_)
  have e₂ := e₁.frame kb₂ x₂ f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
  have ht₂ := ht₁.frame sy₂ (kb₂.rd.trans kb₁.rd.symm) (kb₂.wr.trans kb₁.wr.symm) (kb₂.sp.trans kb₁.sp.symm)
    f₂ (cov_w hp kb₁ ⟨hp.scw,hp.scb⟩ (o:=yOff P i) (l:=1024) (hp.fs hpo.le))
  refine WPs.single (WP.mono_syms (nttW_ok hp hpo kb₂ p₂ ht₂) fun s₃ ⟨kb₃, f₃, p₃, x₃⟩ sy₃ => ?_)
  have e₃ := e₂.frame kb₃ x₃ f₃ fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
    · exact dfar hp (by omega) (by kom) (.inl (by kom))
  have ht₃ := ht₂.frame sy₃ (kb₃.rd.trans kb₂.rd.symm) (kb₃.wr.trans kb₂.wr.symm) (kb₃.sp.trans kb₂.sp.symm)
    f₃ (covers_cons (cov_s hp kb₂ hpo.le) (cov_s hp kb₂ (o:=NS) (l:=1024) (by kom)))
  refine ⟨⟨e₃.kb,e₃.x24,fun i' hi' => ?_⟩,
    ((f₁.mono (by simp)).trans (f₂.mono (by simp))).trans (f₃.mono (by simp)),ht₃⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact e₃.u i' hi'
  · refine (congrArg (fun x => PolyIsW 16 s₃.mem (sA (deL P) s₀ (yOff P i')) (ntt x)) ?_).mp p₃
    simp only [KPke.dcU, cD, deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.params]

/-- What decoding `û'` writes. -/
def uWritesW (P : KemLay) (s₀ : State) : List Region :=
  [R (kA s₀) (deL P).sc (YH P) (1024*P.k),R (kA s₀) (deL P).sc NS 1024,R (kA s₀) (deL P).sc (PP P) 1024]

theorem uW_all {s₀ s : State} (hp : Pre P (deL P) s₀) (hc : Calls P)
    (ht : Optimized.TransformTables s) (h : DInvW P s₀ 0 s) :
    WPs ((List.range P.k).map (Impl.MlKem.AArch64.Optimized.deU P)) s fun t =>
      DInvW P s₀ P.k t ∧ Frame (uWritesW P s₀) s.mem t.mem ∧ Optimized.TransformTables t := by
  apply WPs.range (I := fun i t => DInvW P s₀ i t ∧ Frame (uWritesW P s₀) s.mem t.mem ∧
    Optimized.TransformTables t)
  · intro i hi t ⟨di,fi,ti⟩
    refine WP.mono (uW_step hp hc hi ti di) fun u ⟨du,fu,tu⟩ => ⟨du,fi.trans (fu.sub (fun r hh => ?_)),tu⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl
    · exact ⟨_,by simp [uWritesW],fun _ hh => hh⟩
    · exact ⟨R (kA s₀) (deL P).sc (YH P) (1024*P.k),by simp [uWritesW],
        R.sub2 (by simp [yOff]) (by simp only [yOff]; omega)⟩
    · exact ⟨_,by simp [uWritesW],fun _ hh => hh⟩
  · exact ⟨h,Frame.refl _ _,ht⟩

theorem m_tailW {s₀ s : State} (hp : Pre P (deL P) s₀) (hc : Calls P)
    (ht : Optimized.TransformTables s)
    (hk : KB P (deL P) s₀ s) (hx : s.gpr .x24=1)
    (t₄ : PolyIsW 16 s.mem (sA (deL P) s₀ (TP P))
      (KPke.dotK (dcS (KPke.dkPke P.params (dkD P s₀)))
        (fun j => ntt (KPke.dcU P.params (cD P s₀) j)) P.k)) :
    WPs [Ntt16.Readonly.nttInvAtWithW (TP P) NS,Kem16.widenAt (TP P) (PP P),
      P.ddLAt .x26 (32*P.du*P.k) P.dv (EP P),subAt (EP P) (PP P),ceAt (EP P) 1 .x28 MB] s
      fun t => KB P (deL P) s₀ t ∧ t.gpr .x24=1 ∧ bytesAt t.mem (sA (deL P) s₀ MB) 32=mD P s₀ := by
  have hw := hp.wf
  refine WPs.cons (WP.mono (invW_ok hp (po_TP hw) hk t₄.1 ht) fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  rw [t₄.2] at t₅
  refine WPs.cons (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (by lom) kb₅ t₅)
    fun s₆ ⟨kb₆, f₆, t₆, x₆⟩ => ?_)
  have fv : 32 * P.du * P.k + 32 * P.dv ≤ (deL P).len 1 := by
    simp only [deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.ctLen]
    rw [Nat.mul_add, Nat.mul_assoc]
  refine WPs.cons (WP.mono (ddL_ok hp hc (k := 1) (o := 32 * P.du * P.k) (d := P.dv) (off := EP P) (by decide)
    fv (.inr rfl) (po_EP hw) (.inl (by dek)) kb₆) fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  rw [slice_eq kb₆ (b := 1) (by decide) fv] at p₇
  have t₇ := polyIs_frame f₇ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_PP hw) (po_EP hw) (by lom)) t₆
  refine WPs.cons (WP.mono (sub_ok hp (po_EP hw) (po_PP hw) (by lom) kb₇ p₇.1 t₇.1)
    fun s₈ ⟨kb₈, f₈, p₈, x₈⟩ => ?_)
  rw [p₇.2, t₇.2] at p₈
  refine WPs.single (WP.mono (ce_ok hp (off := EP P) (d := 1) (k := 3) (o := MB) (po_EP hw) (by decide)
    (by decide) (by dek) (by dek) (.inr ⟨by kom, .inl (by kom)⟩) kb₈ p₈.1) fun s₉ ⟨kb₉, f₉, b₉, x₉⟩ => ?_)
  refine ⟨kb₉, by rw [x₉, x₈, x₇, x₆, x₅, hx], ?_⟩
  rw [show sA (deL P) s₀ MB = kA s₀ ((deL P).slot 3) + BitVec.ofNat 64 MB from rfl, b₉, p₈.2, mD, KPke.decM,
    KPke.kpkeDecrypt_eq]
  rfl

end VG.Proof.MlKem.AArch64.Decaps
