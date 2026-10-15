module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.KgA
meta import VerifiedGarbage.Proof.MlKem.AArch64.KgA

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
theorem g_using_ok (hash : FixedHash.HashFn)
 (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩]) {s₀ : State} (hp : Pre P s₀) {s : State} (h : AfterPro P s₀ s) :
    WP isa (FixedHashCallers.kgGUsing hash) s (AfterA P s₀) := by
  have hw := hp.wf
  have f : ∀ {o l : Nat}, o + l ≤ 960 → o + l ≤ kL P 3 := fun h => by simp only [kL]; lom
  have e : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = kA s₀ 3 + BitVec.ofNat 64 o := fun o => by
    rw [h.kb.x28]
  refine WP.mono (hG (hsetup hp h.kb (by decide : 72 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => ?_) (fun p hp' => ?_) ?_) fun s' ⟨k', o'⟩ => ?_
  · rcases mem2' hp' with rfl | rfl
    · exact pieceOk (b := 0) hp h.kb (by decide) (by kl) (by decide) (by decide) (by decide)
    · exact pieceOk (b := 3) hp h.kb (by decide) (f (by decide)) (by decide) (by decide) (by decide)
  · rcases mem2' hp' with rfl | rfl
    · exact pieceOk (b := 3) hp h.kb (by decide) (f (by decide)) (by decide) (by decide) (by decide)
    · exact pieceOk (b := 3) hp h.kb (by decide) (f (by decide)) (by decide) (by decide) (by decide)
  · refine List.pairwise_pair.mpr ?_
    simp only [preg, e]
    exact hp.args.rdisj (by decide) (by decide) (f (by decide)) (f (by decide)) (by decide)
  have kb' := h.kb.hash hp k' fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨3, SB, 32, rfl, by decide, by decide, f (by decide), .inr (.inr (by lom))⟩
    · exact ⟨3, SG, 32, rfl, by decide, by decide, f (by decide), .inr (.inr (by lom))⟩
  have msg : (List.map (pbytes s) [⟨.x25, 0, 32⟩, ⟨.x28, BK, 1⟩]).flatten =
      dB s₀ ++ [BitVec.ofNat 8 P.k] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      h.kb.x25, e]
    rw [show kA s₀ 0 = kA s₀ 0 from rfl, KB.d h.kb, h.bk]
  obtain ⟨o₁, o₂, -⟩ := o'
  rw [msg, e] at o₁ o₂
  have hG := G_eq (dB s₀ ++ [BitVec.ofNat 8 P.params.k])
  refine ⟨kb', by rw [k'.cs _ (by decide) (by decide), h.x24], ?_, ?_⟩
  · rw [o₁, KPke.kgRho, hG]; rfl
  · rw [o₂, KPke.kgSigma, hG]; rfl

 theorem a_using_ok (hash : FixedHash.HashFn)
 (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩])
 {s₀ : State} (hp : Pre P s₀) : WP isa (FixedHashCallers.kgAUsing hash P) s₀ (AfterA P s₀) :=
 WP.seq (WP.mono (prologue_ok hp) fun _ h=>g_using_ok hash hG hp h)
end VG.Proof.MlKem.AArch64.KeyGen
