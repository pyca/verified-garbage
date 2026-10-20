module

public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

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
  have kb₃ := kb₂.hash hp k₃ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨3, KP, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
    · exact ⟨3, RB, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
  have msg : (List.map (pbytes s₂) [⟨.x28, MB, 32⟩, ⟨.x25, 768 * P.k + 32, 32⟩]).flatten =
      mD P s₀ ++ KPke.dkH P.params (dkD P s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₂, kb₂.x25]
    rw [m₂, slice_eq kb₂ (b := 0) (by decide) (by dek)]
    rfl
  obtain ⟨o₁, o₂, -⟩ := o₃
  rw [msg] at o₁ o₂
  have hG := G_eq (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))
  have kp₃ : bytesAt s₃.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [← e28 kb₂, o₁]; show _ = (G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))).1; rw [hG]; rfl
  have r₃ : bytesAt s₃.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2 := by
    rw [← e28 kb₂, o₂]; show _ = (G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))).2; rw [hG]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  have m₃ : bytesAt s₃.mem (sA (deL P) s₀ MB) 32 = mD P s₀ := by
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
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by kom)
  have far₄ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
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


theorem a_tail {s₀ s₂ : State} (hp : Pre P (deL P) s₀)
    (kb₂ : KB P (deL P) s₀ s₂) (x₂ : s₂.gpr .x24=1) (m₂ : bytesAt s₂.mem (sA (deL P) s₀ MB) 32=mD P s₀) :
    WP isa (seqs [hashWith keccak.callee .x28 ST WK 72 6
      [⟨.x28,MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KP,32⟩,⟨.x28,RB,32⟩],
      .block (copy32 .x25 (768*P.k) .x28 SB)]) s₂ (AfterA P s₀) :=
  a_tail_using _ (FixedHash.hashWith_correct keccak _ _ _ _ _ _ _) hp kb₂ x₂ m₂

end VG.Proof.MlKem.AArch64.Decaps
