module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encrypt
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps

/-! # The 16-bit hashing encapsulation is correct

`using_correctHW`: `Kem16.encaps`, as `Hybrid.using_correctH`, with the matrix
sampled with 16 bits and the 16-bit encryption (`encrypt_restW`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Encaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem
variable {P : KemLay}

/-- `Done` with `Â` stored with 16 bits. -/
structure DoneW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (kA s₀ 2) 32 = (gE P s₀).1
  ct : bytesAt s.mem (kA s₀ 3) P.ctLen = KPke.ct P.params (aMW true P (enL P) s₀ mB) (ekE P s₀) (mE s₀) (gE P s₀).2

theorem post_ofW {s₀ sB s' : State} {mA : Mem} (hB : BInvW true P (enL P) s₀ mA (rhoE P s₀) (P.k * P.k) sB)
    (hD : DoneW P s₀ sB.mem (sB.gpr .x24) s') : (encapsAArch64 P).post s₀ s' := by
  show Outcome (fun iters => encapsInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) P.ekLen)
    (bytesAt s₀.mem (s₀.gpr .x1) 32)) ((s'.gpr .x0).setWidth 32)
    (bytesAt s'.mem (s₀.gpr .x2) 32, bytesAt s'.mem (s₀.gpr .x3) P.ctLen)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 = (gE P s₀).1 := hD.key
  have ct : bytesAt s'.mem (s₀.gpr .x3) P.ctLen =
      KPke.ct P.params (aMW true P (enL P) s₀ sB.mem) (ekE P s₀) (mE s₀) (gE P s₀).2 := hD.ct
  rw [key, ct, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show encapsInternal P.params 280 (ekE P s₀) (mE s₀) = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_some (p := P.params) ⟨rfl, rfl⟩
      (a := aMW true P (enL P) s₀ sB.mem) fun i hi j hj => hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show encapsInternal P.params 280 (ekE P s₀) (mE s₀) = none
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_none (p := P.params) hi hj hn]
    rfl

end VG.Proof.MlKem.AArch64.Encaps

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps
open VG.Proof.MlKem.AArch64.Optimized
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay} {prf : Nat→Nat→Prog isa}

/-- Noise, `u`, `v` and the epilogue of `Kem16.encaps`. -/
theorem restHW_ok (valid : PrfValidW P (enL P) prf) {s₀ : State} (hp : Pre P (enL P) s₀) (hr : Noise.Room P)
    (hc : Calls P) {sB : State}
    (htr : Optimized.TransformTables sB)
    (hT : AfterTW true P s₀ (rhoE P s₀) sB)
    (ht : Dot.GammaArtifact sB.mem (sB.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨sB.syms "VG_MLKEM_GAMMA",512⟩] (sB.rd++sB.wr))
    (ha : ∀r∈encW P (enL P) s₀ 2 0, (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn : ∀r∈Noise.allWrites P false (kA s₀ (enL P).sc), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Kem16.enRest prf P) sB (DoneW P s₀ sB.mem (sB.gpr .x24)) := by
  have hB := hT.b
  have e0 : EInvW true P (enL P) s₀ 2 0 sB.mem sB.mem (sB.gpr .x24) (gE P s₀).2 (mE s₀) 0 0 sB :=
    ⟨hB.kb, rfl, hT.r, hT.m, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  refine WP.seq (WP.mono (encrypt_restW valid hp hr hc encArgs (T := ekT (ekE P s₀)) (ekT_eq s₀) htr e0 ht
    hcT ha hn) fun s₁ ⟨mN,fN,e₁,v₁⟩ => ?_)
  refine WP.mono (epilogue_ok hp e₁.kb) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, e₁.x24], ?_, ?_⟩
  · rw [hm,bytesAt_frame e₁.fr (fun r hh => key_far hp (.inr hh)) (by decide)]
    have hf : ∀r∈Noise.allWrites P false (kA s₀ (enL P).sc), (Region.mk (kA s₀ 2) 32).Disjoint r := by
      have hfar := Kem.noise_far hp hr (b := 2) (o := 0) (l := 32) (by enk) (by enk) (.inl (by enk))
      simpa only [R,ptr_zero] using hfar
    rw [bytesAt_frame fN hf (by decide)]; exact hT.key
  · rw [hm]
    exact ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aMW true P (enL P) s₀ sB.mem) (gE P s₀).2 i))
      (fun i hi => by have := e₁.u i hi; rwa [Nat.zero_add] at this) (by rwa [Nat.zero_add] at v₁)

/-- **The 16-bit hashing encapsulation is correct.** -/
theorem using_correctHW (hash : FixedHash.HashFn) (valid : PrfValidW P (enL P) prf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]
      [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) {s₀ : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P s₀)
    (ho : HashOk P) (hr : Noise.Room P) (hc : Calls P) (tables : Tables s₀) (ts : TStk s₀)
    (depthM : (Impl.MlKem.AArch64.Hybrid.matrixH P true).aarch64Depth≤8)
    (depthT : (Impl.MlKem.AArch64.Hybrid.tailH hash).aarch64Depth≤1) :
    WP isa (Impl.MlKem.AArch64.Kem16.encaps hash prf P) s₀ fun t =>
      abiPreserved s₀ t ∧ (encapsAArch64 P).post s₀ t := by
  have hw := hp.wf
  refine WP.seq (WP.mono_syms (WP.tablesDepth (startH_ok hp) tables
    (by unfold Impl.MlKem.AArch64.Hybrid.startH; exact Nat.zero_le _)) fun uA ⟨hA, ta⟩ syA => ?_)
  have tsA : TStk uA := ts.of syA (by rw [hA.kb.sp])
  have mt : MT3 P s₀ uA := ⟨matrix_table_of_kb hp hA.kb ta, by rw [← hA.kb.sp]; exact tsA.shuffle⟩
  have h0 : HInvW true P s₀ uA.mem (rhoE P s₀) (ekE P s₀) 0 0 uA :=
    ⟨BInvW.zero hA.kb hA.x24 hA.rho, Frame.refl _ _, by rw [hstate_zero]; exact hA.zero⟩
  refine WP.seq (WP.mono_syms (WP.tables128 (matrixH_ok hp hk ho h0 mt) ta tsA depthM)
    fun uB ⟨⟨hB, _⟩, tb⟩ _ => ?_)
  have hm : bytesAt uB.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame hB.fr (mb_bW3 hp hk) (by decide)]; exact hA.m
  have hst := hB.hash
  rw [hstate_done (by
    have := ho.three
    have : (ekE P s₀).length = P.ekLen := bytesAt_length _ _ _
    simp only [Impl.MlKem.AArch64.Hybrid.hashPairs, Impl.MlKem.AArch64.Hybrid.blocks]
    omega)] at hst
  refine WP.seq (WP.mono (WP.tablesDepth (tailH_ok hash hG hp hB.b hm hst) tb depthT) fun uC ⟨hC, tc⟩ => ?_)
  refine WP.mono (restHW_ok valid hp hr hc tc.transforms hC tc.gamma tc.gammaRead
    (readonly_enc hp hC.b.kb encArgs tc.gammaApart tc.gammaStack)
    (readonly_noise hp hr hC.b.kb tc.gammaApart)) fun t ht => ⟨ht.abi, post_ofW hC.b ht⟩

end VG.Proof.MlKem.AArch64.Hybrid
