module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd
meta import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
theorem hek_using_ok (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (kb : KB P s₀ s)
    (h : EndInv P s₀ mB v s) :
    WP isa (hash .x28 ST WK 136 6 [⟨.x26, 0, P.ekLen⟩] [⟨.x27, 768 * P.k + 32, 32⟩]) s
      fun s' => KB P s₀ s' ∧ EndInv P s₀ mB v s' ∧
      bytesAt s'.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
        H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) := by
  have hw := hp.wf
  have e28 : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = kA s₀ 3 + BitVec.ofNat 64 o := fun o => by rw [kb.x28]
  refine WP.mono (hH (hsetup hp kb (by decide : 136 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 1) hp kb (by decide) (by kl) (by decide) (by kl) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 2) hp kb (by decide) (by kl) (by kl) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ?_
  have kb' := kb.hash hp k' fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨2, 768 * P.k + 32, 32, rfl, by decide, by decide, by kl, .inl (by decide)⟩
  have msg : (List.map (pbytes s) [⟨.x26, 0, P.ekLen⟩]).flatten = KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb.x26, ptr_zero]
    exact ek_at (T := tV P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h.tl.ek i hi).1) h.rek
  obtain ⟨o, -⟩ := o'
  rw [msg, kb.x27] at o
  refine ⟨kb', h.frame hp kb' (k'.cs _ (by decide) (by decide)) k'.frame fun r hr => ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil] at hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · rw [VG.Proof.MlKem.AArch64.STr, e28]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [VG.Proof.MlKem.AArch64.WKr, e28]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [kb.sp]; exact far_below hp
    · simp only [preg, kb.x27]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  · rw [o, H_eq]; rfl

/-- `z` into `dk`, and the rest. -/
theorem end_using_ok (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : TL P s₀ mB v P.k s) :
    WP isa (FixedHashCallers.kgEndUsing hash P) s (Done P s₀ mB v) := by
  have hw := hp.wf
  refine WP.seq (WP.mono (rho_ok hp h) fun s₁ ⟨kb₁, h₁⟩ => WP.seq (WP.mono (hek_using_ok hash hH hp kb₁ h₁)
    fun s₂ ⟨kb₂, h₂, hh₂⟩ => ?_))
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 0) (D := kA s₀ 2) (so := 32) (dO := 768 * P.k + 64) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb₂.x25 kb₂.x27 (cov_r hp kb₂ (b := 0) (by decide) (by kl))
    (cov_w hp kb₂ (b := 2) (by decide) (by kl))) fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  have kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k + 64) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have far₃ : ∀ r ∈ [R (kA s₀) 2 (768 * P.k + 64) 32], Far P s₀ r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  have h₃ := h₂.frame hp kb₃ (k₃.get .x24) f₃ far₃
  have hh₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
      H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) := by
    rw [bytesAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact hh₂
  have z₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 64)) 32 = zB s₀ := by rw [b₃]; exact kb₂.z
  have ek₃ : bytesAt s₃.mem (kA s₀ 1) P.ekLen = KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) :=
    ek_at (T := tV P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h₃.tl.ek i hi).1) h₃.rek
  have dk₃ : bytesAt s₃.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) ++ H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) ++ zB s₀ :=
    dk_at (cat_at (T := KPke.kgS P.params (dB s₀)) fun j hj => h₃.tl.dk j hj)
      (ek_at (T := tV P s₀ mB) (ρ := rhoK P s₀) (fun i hi => by rw [ptr_add]; exact (h₃.tl.ek i hi).2)
        (by rw [ptr_add, show 384 * P.k + 384 * P.k = 768 * P.k by omega]; exact h₃.rdk)) hh₃ z₃
  refine WP.mono (restore_ok hp kb₃) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, h₃.tl.c.x24], ?_, ?_⟩
  · rw [hm]; exact ek₃
  · rw [hm]; exact dk₃

end VG.Proof.MlKem.AArch64.KeyGen
