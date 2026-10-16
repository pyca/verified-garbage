module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Encaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
theorem a_using_ok (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6 [⟨.x25,0,P.ekLen⟩] [⟨.x28,HB,32⟩])
 (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6 [⟨.x28,MB,32⟩,⟨.x28,HB,32⟩]
  [⟨.x26,0,32⟩,⟨.x28,RB,32⟩]) {s₀ : State} (hp : Pre P (enL P) s₀) : WP isa (FixedHashCallers.enAUsing hash P) s₀ (AfterA P s₀) := by
  have hw := hp.wf
  -- the prologue and `m`
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok hp) fun s₁ h₁ => ?_
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 1) (D := kA s₀ 4) (so := 0) (dO := MB) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by enk) (by enk) (by enk) (hp.fs (by lom)) (by enk)
      (by decide)) (by rw [h₁.keep.get .x1 (by decide)]; rfl) h₁.kb.x28
    (cov_r hp h₁.kb (b := 1) (by enk) (by enk)) (cov_s hp h₁.kb (by lom)))
    fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  have kb₂ := h₁.kb.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by enk)
  have m₂ : bytesAt s₂.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [show sA (enL P) s₀ MB = kA s₀ 4 + BitVec.ofNat 64 MB from rfl, b₂,
      h₁.kb.ro_bytes (b := 1) (by enk) (by enk), ptr_zero]
  have x24₂ : s₂.gpr .x24 = 1 := by rw [k₂.get .x24, h₁.x24]
  -- `H(ek)`
  refine WP.seq (WP.mono (hH (hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 0) hp kb₂ (by decide) (by enk) (.inl (by enk)) (by enk) (by enk))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₂ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ := kb₂.hash hp k₃ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, HB, 32, rfl, by decide, by enk, by enk, .inr (.inr (by enk))⟩
  have hek : bytesAt s₂.mem (s₂.gpr .x25 + BitVec.ofNat 64 0) P.ekLen = ekE P s₀ := by
    rw [kb₂.x25, ptr_zero]
    exact kb₂.ro (b := 0) (by enk)
  have h₃ : bytesAt s₃.mem (sA (enL P) s₀ HB) 32 = H (ekE P s₀) := by
    obtain ⟨o, -⟩ := o₃
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₂] at o
    rw [hek] at o
    rw [o, H_eq]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  have m₃ : bytesAt s₃.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame k₃'.frame (fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp (by enk) (by enk) (by decide)
      · exact sdisj hp (by enk) (by enk) (by decide)
      · exact below_R hp hp.scb (by enk)
      · exact sdisj hp (by enk) (by enk) (by decide)) (by decide)]
    exact m₂
  -- `G(m ‖ H(ek))`
  refine WP.seq (WP.mono (hG (hsetup hp kb₃ (by decide : 72 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk)
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 1) hp kb₃ (by decide) (by enk) (.inl (by enk)) (by decide) (by enk)
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, kb₃.x26, e28 kb₃]
      exact hp.args.rdisj (by enk) (by enk) (by enk) (by enk) (by enk) (by enk)))
    fun s₄ ⟨k₄, o₄⟩ => ?_)
  have kb₄ := kb₃.hash hp k₄ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨1, 0, 32, rfl, by decide, by enk, by enk, .inl (by enk)⟩
    · exact ⟨3, RB, 32, rfl, by decide, by enk, by enk, .inr (.inr (by enk))⟩
  have msg : (List.map (pbytes s₃) [⟨.x28, MB, 32⟩, ⟨.x28, HB, 32⟩]).flatten = mE s₀ ++ H (ekE P s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₃]
    rw [m₃, h₃]
  obtain ⟨o₁, o₂, -⟩ := o₄
  rw [msg] at o₁ o₂
  have hG := G_eq (mE s₀ ++ H (ekE P s₀))
  have key₄ : bytesAt s₄.mem (kA s₀ 2) 32 = (gE P s₀).1 := by
    have e : kA s₀ 2 = s₃.gpr .x26 + BitVec.ofNat 64 0 := by rw [kb₃.x26, ptr_zero]; rfl
    rw [e, o₁]; show _ = (G (mE s₀ ++ H (ekE P s₀))).1; rw [hG]; rfl
  have r₄ : bytesAt s₄.mem (sA (enL P) s₀ RB) 32 = (gE P s₀).2 := by
    rw [← e28 kb₃, o₂]; show _ = (G (mE s₀ ++ H (ekE P s₀))).2; rw [hG]; rfl
  have k₄' := k₄
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₃.x28, kb₃.x26, kb₃.sp] at k₄'
  have m₄ : bytesAt s₄.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame k₄'.frame (fun r hr => by
      rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
      · exact sdisj hp (by enk) (by enk) (by decide)
      · exact sdisj hp (by enk) (by enk) (by decide)
      · exact below_R hp hp.scb (by enk)
      · exact hp.args.rdisj (by enk) (by enk) (by enk) (by enk) (by enk) (by enk)
      · exact sdisj hp (by enk) (by enk) (by decide)) (by decide)]
    exact m₃
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 4) (so := 384 * P.k) (dO := SB) (by decide)
    (by decide) (by lom) (by decide) (hp.args.rdisj (by enk) (by enk) (by enk)
      (hp.fs (by lom)) (by enk) (by enk)) kb₄.x25 kb₄.x28 (cov_r hp kb₄ (b := 0) (by enk)
      (by enk)) (cov_s hp kb₄ (by lom)))
    fun s₅ ⟨k₅, f₅, b₅⟩ => ?_
  have kb₅ := kb₄.frame k₅ f₅ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by enk)
  have far₅ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₅.mem (sA (enL P) s₀ o) l = bytesAt s₄.mem (sA (enL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₅ (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by lom) h
  refine ⟨kb₅, by rw [k₅.get .x24, k₄.cs _ (by decide) (by decide), k₃.cs _ (by decide) (by decide), x24₂], ?_,
    by rw [far₅ (o := RB) (l := 32) (by lom) (by decide)]; exact r₄,
    by rw [far₅ (o := MB) (l := 32) (by lom) (by decide)]; exact m₄, ?_⟩
  · rw [bytesAt_frame f₅ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hp.args.disj 2 (by enk) 4 (by enk) (by decide) (by enk)).sub_right
        (R.sub (hp.fs (by lom)))) (by decide)]
    exact key₄
  · rw [show sA (enL P) s₀ SB = kA s₀ 4 + BitVec.ofNat 64 SB from rfl, b₅,
      kb₄.ro_bytes (b := 0) (by enk) (by enk),
      ← bytesAt_slice _ _ (show 384 * P.k + 32 ≤ P.ekLen from Nat.le_refl _)]
    rfl

end VG.Proof.MlKem.AArch64.Encaps
