module

public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.VRest
import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! ### `MlKem.AArch64.Optimized.DecryptSeed`, which only this module used -/

section

/-! # Decapsulation seed derivation after the fused decryption path -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem a_tail_using (hash : FixedHash.HashFn)
    (hash_ok : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x28,MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KP,32⟩,⟨.x28,RB,32⟩])
    {s₀ s₂ : State} (hp : Pre P (deL P) s₀)
    (kb₂ : KB P (deL P) s₀ s₂) (x₂ : s₂.gpr .x24=1) (m₂ : bytesAt s₂.mem (sA (deL P) s₀ MB) 32=mD P s₀) :
    WP isa (seqs [hash .x28 ST WK 72 6
      [⟨.x28,MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KP,32⟩,⟨.x28,RB,32⟩],
      .block (copy32 .x25 (768*P.k) .x28 SB)]) s₂ (AfterA P s₀) := by
  have hw := hp.wf
  -- `G(m' ‖ h)`
  refine WP.seq (WP.mono (hash_ok (hsetup hp kb₂ (by decide : 72 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek)
      · exact pieceOk (k := 0) hp kb₂ (by decide) (by dek) (.inl (by dek)) (by decide) (by dek))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek)
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, e28 kb₂]
      exact sdisj hp (by kom) (by kom) (by decide)))
    fun s₃ ⟨k₃, o₃⟩ => ?_)
  obtain kb₃ := kb₂.hash hp k₃ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨3, KP, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
    · exact ⟨3, RB, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
  obtain msg : (List.map (pbytes s₂) [⟨.x28, MB, 32⟩, ⟨.x25, 768 * P.k + 32, 32⟩]).flatten =
      mD P s₀ ++ KPke.dkH P.params (dkD P s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₂, kb₂.x25]
    rw [m₂, slice_eq kb₂ (b := 0) (by decide) (by dek)]
    rfl
  obtain ⟨o₁, o₂, -⟩ := o₃
  rw [msg] at o₁ o₂
  obtain hG := G_eq (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))
  obtain kp₃ : bytesAt s₃.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [← e28 kb₂, o₁]; show _ = (G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))).1; rw [hG]; rfl
  obtain r₃ : bytesAt s₃.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2 := by
    rw [← e28 kb₂, o₂]; show _ = (G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))).2; rw [hG]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  obtain m₃ : bytesAt s₃.mem (sA (deL P) s₀ MB) 32 = mD P s₀ := by
    rw [bytesAt_frame k₃'.frame (fun r hr => by
      rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
      · exact sdisj hp (by kom) (by kom) (by decide)
      · exact sdisj hp (by kom) (by kom) (by decide)
      · exact below_R hp hp.scb (hp.fs (by kom))
      · exact sdisj hp (by kom) (by kom) (by decide)
      · exact sdisj hp (by kom) (by kom) (by decide)) (by decide)]
    exact m₂
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 3) (so := 768 * P.k) (dO := SB) (by decide)
    (by decide) (by kom) (by decide) (hp.args.rdisj (by dek) (by dek) (by dek) (hp.fs (by kom)) (by dek)
      (by dek)) kb₃.x25 kb₃.x28 (cov_r hp kb₃ (b := 0) (by dek) (by dek)) (cov_s hp kb₃ (by kom)))
    fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  obtain kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by kom)
  obtain far₄ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₄.mem (sA (deL P) s₀ o) l = bytesAt s₃.mem (sA (deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₄ (fun r hr => ?_) (by kom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by kom) h
  refine ⟨kb₄, by rw [k₄.get .x24, k₃.cs _ (by decide) (by decide), x₂],
    by rw [far₄ (o := MB) (l := 32) (by kom) (by decide)]; exact m₃,
    by rw [far₄ (o := KP) (l := 32) (by kom) (by decide)]; exact kp₃,
    by rw [far₄ (o := RB) (l := 32) (by kom) (by decide)]; exact r₃, ?_⟩
  rw [show sA (deL P) s₀ SB = kA s₀ 3 + BitVec.ofNat 64 SB from rfl, b₄,
    show kA s₀ 0 = kA s₀ ((deL P).slot 0) from rfl, slice_eq kb₃ (b := 0) (by decide) (by dek)]
  rfl

end VG.Proof.MlKem.AArch64.Decaps

end

end

/-! ### `MlKem.AArch64.Optimized.DecryptM`, which only this module used -/

section

/-! ### `MlKem.AArch64.Optimized.DecryptW`, which only this module used -/

section

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
    (R.sub2 (by simp only [yOff]; omega_using []) (by simp only [yOff]; omega_using [hi]))) (h.u i hi)⟩

theorem uW_step {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) {i : Nat} (hi : i < P.k) {s : State}
    (ht : Optimized.TransformTables s) (h : DInvW P s₀ i s) :
    WP isa (Impl.MlKem.AArch64.Optimized.deU P i) s fun t => DInvW P s₀ (i + 1) t ∧
      Frame [R (kA s₀) (deL P).sc (PP P) 1024,R (kA s₀) (deL P).sc (yOff P i) 1024,
        R (kA s₀) (deL P).sc NS 1024] s.mem t.mem ∧ Optimized.TransformTables t := by
  have hw := hp.wf
  obtain hpo := po_y hw hi
  obtain hu := du_le hi
  obtain fu : 32 * P.du * i + 32 * P.du ≤ (deL P).len 1 := by dek
  apply WPs.seqs (by simp)
  refine WPs.cons (WP.mono_syms (ddL_ok hp hc (k := 1) (o := 32 * P.du * i) (d := P.du) (off := PP P)
    (by decide) fu (.inl rfl) (po_PP hw) (.inl (by dek)) h.kb) fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ sy₁ => ?_)
  obtain e₁ := h.frame kb₁ x₁ f₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega_using [hi]) (po_PP hw).le (by lom)
  rw [slice_eq h.kb (b := 1) (by decide) fu] at p₁
  obtain ht₁ := ht.frame sy₁ (kb₁.rd.trans h.kb.rd.symm) (kb₁.wr.trans h.kb.wr.symm) (kb₁.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=PP P) (l:=1024) (hp.fs (po_PP hw).le))
  refine WPs.cons (WP.mono_syms (narrowW_ok hp (po_PP hw) hpo (by lom) kb₁ p₁)
    fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ sy₂ => ?_)
  obtain e₂ := e₁.frame kb₂ x₂ f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega_using [hi]) hpo.le (.inr (by simp only [yOff]; omega_using []))
  obtain ht₂ := ht₁.frame sy₂ (kb₂.rd.trans kb₁.rd.symm) (kb₂.wr.trans kb₁.wr.symm) (kb₂.sp.trans kb₁.sp.symm)
    f₂ (cov_w hp kb₁ ⟨hp.scw,hp.scb⟩ (o:=yOff P i) (l:=1024) (hp.fs hpo.le))
  refine WPs.single (WP.mono_syms (nttW_ok hp hpo kb₂ p₂ ht₂) fun s₃ ⟨kb₃, f₃, p₃, x₃⟩ sy₃ => ?_)
  obtain e₃ := e₂.frame kb₃ x₃ f₃ fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact dfar hp (by omega_using [hi]) hpo.le (.inr (by simp only [yOff]; omega_using []))
    · exact dfar hp (by omega_using [hi]) (by kom) (.inl (by kom))
  obtain ht₃ := ht₂.frame sy₃ (kb₃.rd.trans kb₂.rd.symm) (kb₃.wr.trans kb₂.wr.symm) (kb₃.sp.trans kb₂.sp.symm)
    f₃ (covers_cons (cov_s hp kb₂ hpo.le) (cov_s hp kb₂ (o:=NS) (l:=1024) (by kom)))
  refine ⟨⟨e₃.kb,e₃.x24,fun i' hi' => ?_⟩,
    ((f₁.mono (by simp)).trans (f₂.mono (by simp))).trans (f₃.mono (by simp)),ht₃⟩
  rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
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
        R.sub2 (by simp [yOff]) (by simp only [yOff]; omega_using [hi])⟩
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
  obtain fv : 32 * P.du * P.k + 32 * P.dv ≤ (deL P).len 1 := by
    simp only [deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.ctLen]
    rw [Nat.mul_add, Nat.mul_assoc]
  refine WPs.cons (WP.mono (ddL_ok hp hc (k := 1) (o := 32 * P.du * P.k) (d := P.dv) (off := EP P) (by decide)
    fv (.inr rfl) (po_EP hw) (.inl (by dek)) kb₆) fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  rw [slice_eq kb₆ (b := 1) (by decide) fv] at p₇
  obtain t₇ := polyIs_frame f₇ (fun r hr => by
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

end

end


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
  obtain far : ∀o l, o+l≤P.scl → (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint
      (R (kA s₀) (deL P).sc o l) := by
    intro o l hf
    obtain hd : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) (deL P).sc 0 P.scl) := by
      simpa only [R,ptr_zero] using ha
    exact hd.sub_right (R.sub2 (by omega_using []) (by omega_using [hf]))
  apply WPs.seqs (by simp)
  rw [List.append_assoc]
  apply WPs.append
  refine WPs.mono_syms (uW_all hp hc htr ⟨h.kb,h.x24,fun _ hj => by omega⟩) fun t ⟨dt,ft,trt⟩ hs => ?_
  obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [hs]; apply gamma_frame ht ft
    intro r hh
    simp only [uWritesW, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl <;> exact far _ _ (by lom)
  obtain hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ ((deL P).slot 0)+BitVec.ofNat 64 (0+384*j)) 384)=
      dcS (KPke.dkPke P.params (dkD P s₀)) j := by
    intro j hj
    simp only [deL,Nat.zero_add]
    rw [←bytesAt_slice s₀.mem (kA s₀ 0) (show 384*j+384≤(deL P).len 0 by dek),dcS_eq s₀ hj]
    rfl
  obtain d0 : DecodeInvW P (deL P) s₀ t.mem (dcS (KPke.dkPke P.params (dkD P s₀)))
      (fun j => ntt (KPke.dcU P.params (cD P s₀) j)) 1 0 t :=
    ⟨dt.kb,dt.x24,fun _ hj => by omega,dt.u,Frame.refl _ _⟩
  apply WPs.append
  obtain dec := WPs.range (fun _ hj _ h => decode_stepW hp (kE := 0) (eo := 0) (by decide) (by change 0<2; decide)
    (by dek) hj hT h) d0
  simp only [Nat.zero_add] at dec
  refine WPs.mono_syms dec fun u du hsu => ?_
  obtain gu : Dot.GammaArtifact u.mem (u.syms "VG_MLKEM_GAMMA") := by
    rw [hsu]
    apply gamma_frame gt du.frame
    intro r hh
    rw [List.mem_singleton.mp hh,hs]
    obtain hkk := Nat.mul_le_mul_right P.k hw.facts.1
    simp only [Nat.one_mul] at hkk
    exact far _ _ (by lom)
  obtain cu : Covers [⟨u.syms "VG_MLKEM_GAMMA",512⟩] (u.rd++u.wr) := by
    simpa only [hsu,hs,du.kb.rd,du.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
  obtain au : (polyRegion (sA (deL P) s₀ (TP P))).Disjoint ⟨u.syms "VG_MLKEM_GAMMA",512⟩ := by
    rw [hsu,hs]; exact (far _ _ (by lom)).symm
  obtain tru := trt.frame hsu (du.kb.rd.trans dt.kb.rd.symm) (du.kb.wr.trans dt.kb.wr.symm)
    (du.kb.sp.trans dt.kb.sp.symm) du.frame (cov_w hp dt.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  refine WPs.cons (WP.mono_syms (fusedW_ok hp (po_TP hw) du.kb (decodedTerms P)
    (decoded_readyW hp du gu cu au).data) fun w ⟨kw,fw,pw,xw⟩ hus => ?_)
  rw [decoded_sum] at pw
  obtain trw := tru.frame hus (kw.rd.trans du.kb.rd.symm) (kw.wr.trans du.kb.wr.symm)
    (kw.sp.trans du.kb.sp.symm) fw (cov_w hp du.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  exact m_tailW hp hc trw kw (xw.trans du.x24) pw

end VG.Proof.MlKem.AArch64.Decaps

end

end


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
  obtain gt : Dot.GammaArtifact s₁.mem (s₁.syms "VG_MLKEM_GAMMA") := by
    rw [hs]
    rcases h₁.mem with hm | hf
    · rwa [hm]
    · apply gamma_frame ht hf
      intro r hh
      rw [List.mem_singleton.mp hh]
      exact ha.sub_right (R.sub (by lom))
  obtain ct : Covers [⟨s₁.syms "VG_MLKEM_GAMMA",512⟩] (s₁.rd++s₁.wr) := by
    simpa only [hs,h₁.keep.rd,h₁.keep.wr] using hcT
  obtain tr₁ : Optimized.TransformTables s₁ := by
    apply htr.frame hs h₁.keep.rd h₁.keep.wr h₁.keep.sp
    · rcases h₁.mem with hm | hf
      · simpa only [hm] using Frame.refl [R (kA s₀) (deL P).sc (SV P) 48] s₀.mem
      · exact hf
    · exact cov_w₀ hp ⟨hp.scw,hp.scb⟩ (hp.fs (by omega_using []))
  refine WP.seq (WP.mono (fused_m_ok hp hc tr₁ ⟨h₁.kb,h₁.x24,fun _ hj => by omega⟩ gt ct
    (by simpa only [hs] using ha)) fun s₂ ⟨kb₂,x₂,m₂⟩ => ?_)
  exact a_tail_using hash hash_ok hp kb₂ x₂ m₂

end VG.Proof.MlKem.AArch64.Decaps
