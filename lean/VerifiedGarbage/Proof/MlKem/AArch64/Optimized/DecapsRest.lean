module

public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemEncrypt
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Decapsulation re-encryption, ciphertext checking and implicit rejection -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem fused_c_using_ok (hash : FixedHash.HashFn)
    (hash_ok : FixedHash.HashCorrect hash .x28 ST WK 136 0x1f
      [⟨.x25,768*P.k+64,32⟩,⟨.x26,0,P.ctLen⟩] [⟨.x28,JB,32⟩])
    {s₀ : State} (hp : Pre P (deL P) s₀) (hr : Noise.Room P) (hc : Calls P) {uA sB : State} (hA : AfterA P s₀ uA)
    (htr : Optimized.TransformTables sB)
    (hB : BInv P (deL P) s₀ uA.mem (rhoD P s₀) (P.k * P.k) sB)
    (ht : Dot.GammaArtifact sB.mem (sB.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨sB.syms "VG_MLKEM_GAMMA",512⟩] (sB.rd++sB.wr))
    (ha : ∀r∈encW P (deL P) s₀ 3 (CB P), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn : ∀r∈Noise.allWrites P false (kA s₀ (deL P).sc), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.FixedHashDecaps.deRestUsing hash keccak.callee P) sB (Done P s₀ sB.mem (sB.gpr .x24)) := by
  have hw := hp.wf
  have fbw : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) → (o + l ≤ AH) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) → ∀ r ∈ bW P (deL P) s₀, (R (kA s₀) (deL P).sc o l).Disjoint r :=
    fun f h1 h2 h3 r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp f (by lom) h1
      · exact sdisj hp f (by lom) (.inl h2)
      · exact sdisj hp f (by lom) h3
      · exact below_R hp hp.scb (hp.fs f)
  have r₀ : bytesAt sB.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2 := by
    rw [bytesAt_frame hB.fr (fbw (o := RB) (l := 32) (by dek) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.r
  have m₀ : bytesAt sB.mem (sA (deL P) s₀ MB) 32 = mD P s₀ := by
    rw [bytesAt_frame hB.fr (fbw (o := MB) (l := 32) (by dek) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.m
  have kp₀ : bytesAt sB.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [bytesAt_frame hB.fr (fbw (o := KP) (l := 32) (by dek) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.kp
  have e0 : EInv P (deL P) s₀ 3 (CB P) sB.mem sB.mem (sB.gpr .x24) (gD P s₀).2 (mD P s₀) 0 0 sB :=
    ⟨hB.kb, rfl, r₀, m₀, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  -- `c'`
  refine WP.seq (WP.mono (encrypt_rest hp hr hc (encArgs hw) (T := ekT (KPke.dkEk P.params (dkD P s₀))) (ekT_eq s₀) htr e0 ht hcT ha hn)
    fun s₁ ⟨mN,fN,e₁,v₁⟩ => ?_)
  have kb₁ := e₁.kb
  have c₁ : bytesAt s₁.mem (sA (deL P) s₀ (CB P)) P.ctLen = cpr P s₀ sB.mem :=
    ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aM P (deL P) s₀ sB.mem) (gD P s₀).2 i))
      (fun i hi => by rw [ptr_add]; exact e₁.u i hi) (by rw [ptr_add]; exact v₁)
  have kp₁ : bytesAt s₁.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [bytesAt_frame e₁.fr (far_encW hp (by decide) (by decide) (by decide)) (by decide)]
    have hroom := hr.kem
    rw [bytesAt_frame fN (Kem.noise_far hp hr hp.scb (hp.fs (by lom)) (.inr (by lom))) (by decide)]
    exact kp₀
  -- `K̄ = J(z ‖ c)`
  refine WP.seq (WP.mono (hash_ok (hsetup hp kb₁ (by decide : 136 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 0) hp kb₁ (by decide) (by dek) (.inl (by dek)) (by decide) (by dek)
      · exact pieceOk (k := 1) hp kb₁ (by decide) (by dek) (.inl (by dek)) (by dek) (by dek))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₁ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek))
    (List.pairwise_singleton _ _)) fun s₂ ⟨k₂, o₂⟩ => ?_)
  have kb₂ := kb₁.hash hp k₂ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, JB, 32, rfl, by decide, by dek, by dek, .inr (.inr (by dek))⟩
  have msg : (List.map (pbytes s₁) [⟨.x25, 768 * P.k + 64, 32⟩, ⟨.x26, 0, P.ctLen⟩]).flatten =
      KPke.dkZ P.params (dkD P s₀) ++ cD P s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb₁.x25, kb₁.x26]
    have hc : bytesAt s₁.mem (kA s₀ ((deL P).slot 1)) P.ctLen = cD P s₀ := kb₁.ro (b := 1) (by dek)
    rw [slice_eq kb₁ (b := 0) (by decide) (by dek), ptr_zero, hc]
    rfl
  have jb₂ : bytesAt s₂.mem (sA (deL P) s₀ JB) 32 = jD P s₀ := by
    obtain ⟨o, -⟩ := o₂
    rw [msg, e28 kb₁] at o
    rw [o]; show _ = J (KPke.dkZ P.params (dkD P s₀) ++ cD P s₀); rw [J_eq]; rfl
  have k₂' := k₂
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₁.x28, kb₁.sp] at k₂'
  have far₂ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 840 ≤ o → (o + l ≤ JB ∨ JB + 32 ≤ o) →
      bytesAt s₂.mem (sA (deL P) s₀ o) l = bytesAt s₁.mem (sA (deL P) s₀ o) l := fun f h1 h2 => by
    refine bytesAt_frame k₂'.frame (fun r hr => ?_) (by lom)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact sdisj hp f (by lom) (.inr (by simp only [KEM.ST]; omega))
    · exact sdisj hp f (by lom) (.inr (by simp only [KEM.WK]; omega))
    · exact below_R hp hp.scb (hp.fs f)
    · exact sdisj hp f (by lom) h2
  have c₂ : bytesAt s₂.mem (sA (deL P) s₀ (CB P)) P.ctLen = cpr P s₀ sB.mem := by
    rw [far₂ (by lom) (by lom) (by lom)]; exact c₁
  have kp₂ : bytesAt s₂.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [far₂ (by lom) (by decide) (by decide)]; exact kp₁
  have x24₂ : s₂.gpr .x24 = sB.gpr .x24 := by rw [k₂.cs _ (by decide) (by decide), e₁.x24]
  -- `c = c'`
  refine WP.seq (WP.mono (cmp_ok hp kb₂ c₂) fun s₃ ⟨k₃, m₃, x₃⟩ => ?_)
  have kb₃ := kb₂.block k₃ m₃ (by decide)
  -- the key
  change WP isa (.block (deSel ++ P.kemEpilogue)) s₃ _
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok hp kb₃ (e := decide (cD P s₀ = cpr P s₀ sB.mem)) (by
    rw [x₃]; by_cases h : cD P s₀ = cpr P s₀ sB.mem <;> simp [h])) fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact safe_R hp (b := 2) ⟨by dek, by dek⟩ (by dek) (.inl (by dek))
  refine WP.mono (epilogue_ok hp kb₄) fun s' ⟨abi, x0, hm⟩ => ⟨abi, ?_, ?_⟩
  · rw [x0, k₄.get .x24, k₃.get .x24, x24₂]
  · rw [hm, b₄, m₃, kp₂, jb₂]
    by_cases h : cD P s₀ = cpr P s₀ sB.mem <;> simp [h]


theorem fused_c_ok {s₀ : State} (hp : Pre P (deL P) s₀) (hr : Noise.Room P) (hc : Calls P) {uA sB : State} (hA : AfterA P s₀ uA)
    (htr : Optimized.TransformTables sB)
    (hB : BInv P (deL P) s₀ uA.mem (rhoD P s₀) (P.k * P.k) sB)
    (ht : Dot.GammaArtifact sB.mem (sB.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨sB.syms "VG_MLKEM_GAMMA",512⟩] (sB.rd++sB.wr))
    (ha : ∀r∈encW P (deL P) s₀ 3 (CB P), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn : ∀r∈Noise.allWrites P false (kA s₀ (deL P).sc), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Optimized.deRest keccak.callee P) sB (Done P s₀ sB.mem (sB.gpr .x24)) :=
  fused_c_using_ok _ (FixedHash.hashWith_correct keccak _ _ _ _ _ _ _) hp hr hc hA htr hB ht hcT ha hn

end VG.Proof.MlKem.AArch64.Decaps
