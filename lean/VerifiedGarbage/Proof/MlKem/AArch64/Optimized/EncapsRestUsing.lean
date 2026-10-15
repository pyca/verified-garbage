module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing

public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemEncryptUsing
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Encapsulation output and ABI after fused encryption -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Encaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
variable {prf : Nat→Nat→Prog isa}

theorem fused_c_using_ok (valid : PrfValid P (enL P) prf) {s₀ : State} (hp : Pre P (enL P) s₀) (hr : Noise.Room P) (hc : Calls P) {uA sB : State} (hA : AfterA P s₀ uA)
    (htr : Optimized.TransformTables sB)
    (hB : BInv P (enL P) s₀ uA.mem (rhoE P s₀) (P.k * P.k) sB)
    (ht : Dot.GammaArtifact sB.mem (sB.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨sB.syms "VG_MLKEM_GAMMA",512⟩] (sB.rd++sB.wr))
    (ha : ∀r∈encW P (enL P) s₀ 2 0, (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn : ∀r∈Noise.allWrites P false (kA s₀ (enL P).sc), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Optimized.enRestUsing prf P) sB (Done P s₀ sB.mem (sB.gpr .x24)) := by
  have hw := hp.wf
  have fbw : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) → (o + l ≤ AH) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) → ∀ r ∈ bW P (enL P) s₀, (R (kA s₀) (enL P).sc o l).Disjoint r :=
    fun f h1 h2 h3 r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp f (by lom) h1
      · exact sdisj hp f (by lom) (.inl h2)
      · exact sdisj hp f (by lom) h3
      · exact below_R hp hp.scb (hp.fs f)
  have r : bytesAt sB.mem (sA (enL P) s₀ RB) 32 = (gE P s₀).2 := by
    rw [bytesAt_frame hB.fr (fbw (o := RB) (l := 32) (by lom) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.r
  have m : bytesAt sB.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame hB.fr (fbw (o := MB) (l := 32) (by lom) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.m
  have key : bytesAt sB.mem (kA s₀ 2) 32 = (gE P s₀).1 := by
    rw [bytesAt_frame hB.fr (fun r hr => key_far hp (.inl hr)) (by decide)]; exact hA.key
  have e0 : EInv P (enL P) s₀ 2 0 sB.mem sB.mem (sB.gpr .x24) (gE P s₀).2 (mE s₀) 0 0 sB :=
    ⟨hB.kb, rfl, r, m, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  refine WP.seq (WP.mono (encrypt_rest_using valid hp hr hc encArgs (T := ekT (ekE P s₀)) (ekT_eq s₀) htr e0 ht hcT ha hn) fun s₁ ⟨mN,fN,e₁,v₁⟩ => ?_)
  refine WP.mono (epilogue_ok hp e₁.kb) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, e₁.x24], ?_, ?_⟩
  · rw [hm,bytesAt_frame e₁.fr (fun r hh => key_far hp (.inr hh)) (by decide)]
    have hf : ∀r∈Noise.allWrites P false (kA s₀ (enL P).sc), (Region.mk (kA s₀ 2) 32).Disjoint r := by
      have hfar := Kem.noise_far hp hr (b := 2) (o := 0) (l := 32) (by enk) (by enk) (.inl (by enk))
      simpa only [R,ptr_zero] using hfar
    rw [bytesAt_frame fN hf (by decide)]; exact key
  · rw [hm]
    exact ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aM P (enL P) s₀ sB.mem) (gE P s₀).2 i))
      (fun i hi => by have := e₁.u i hi; rwa [Nat.zero_add] at this) (by rwa [Nat.zero_add] at v₁)


end VG.Proof.MlKem.AArch64.Encaps
