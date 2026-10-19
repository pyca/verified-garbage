module
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encrypt
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise
import VerifiedGarbage.Proof.MlKem.AArch64.DecapsCmp

/-! # The 16-bit decapsulation is correct

`fused_c_W_ok`: the re-encryption of `Kem16.deRest` (`encrypt_restW`), `J(z ‖ c)`,
the comparison and the selection; `using_correctW`:
`Kem16.decaps`, with the matrix sampled with 16 bits. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
variable {prf : Nat→Nat→Prog isa}

/-- `cpr` with `Â` stored with 16 bits. -/
abbrev cprW (P : KemLay) (s₀ : State) (mB : Mem) : List Byte :=
  KPke.ct P.params (aMW true P (deL P) s₀ mB) (KPke.dkEk P.params (dkD P s₀)) (mD P s₀) (gD P s₀).2

/-- `Done` with `Â` stored with 16 bits. -/
structure DoneW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (kA s₀ 2) 32 = if cD P s₀ = cprW P s₀ mB then (gD P s₀).1 else jD P s₀

theorem post_ofW {s₀ sB s' : State} {mA : Mem} (hB : BInvW true P (deL P) s₀ mA (rhoD P s₀) (P.k * P.k) sB)
    (hD : DoneW P s₀ sB.mem (sB.gpr .x24) s') : (decapsAArch64 P).post s₀ s' := by
  show Outcome (fun iters => decapsInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) P.dkLen)
    (bytesAt s₀.mem (s₀.gpr .x1) P.ctLen)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s₀.gpr .x2) 32)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 =
      if cD P s₀ = cprW P s₀ sB.mem then (gD P s₀).1 else jD P s₀ := hD.key
  rw [key, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some (p := P.params) ⟨rfl, rfl⟩
      (a := aMW true P (deL P) s₀ sB.mem) fun i hi j hj => by rw [KPke.ekRho_dkEk]; exact hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = none
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none (p := P.params) hi hj (by rw [KPke.ekRho_dkEk]; exact hn)]
    rfl

theorem fused_c_W_ok (valid : PrfValidW P (deL P) prf) (hash : FixedHash.HashFn)
    (hash_ok : FixedHash.HashCorrect hash .x28 ST WK 136 0x1f
      [⟨.x25,768*P.k+64,32⟩,⟨.x26,0,P.ctLen⟩] [⟨.x28,JB,32⟩])
    {s₀ : State} (hp : Pre P (deL P) s₀) (hr : Noise.Room P) (hc : Calls P) {uA sB : State} (hA : AfterA P s₀ uA)
    (htr : Optimized.TransformTables sB)
    (hB : BInvW true P (deL P) s₀ uA.mem (rhoD P s₀) (P.k * P.k) sB)
    (ht : Dot.GammaArtifact sB.mem (sB.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨sB.syms "VG_MLKEM_GAMMA",512⟩] (sB.rd++sB.wr))
    (ha : ∀r∈encW P (deL P) s₀ 3 (CB P), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn : ∀r∈Noise.allWrites P false (kA s₀ (deL P).sc), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Kem16.deRest hash prf P) sB (DoneW P s₀ sB.mem (sB.gpr .x24)) := by
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
  have e0 : EInvW true P (deL P) s₀ 3 (CB P) sB.mem sB.mem (sB.gpr .x24) (gD P s₀).2 (mD P s₀) 0 0 sB :=
    ⟨hB.kb, rfl, r₀, m₀, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  -- `c'`
  refine WP.seq (WP.mono (encrypt_restW valid hp hr hc (encArgs hw) (T := ekT (KPke.dkEk P.params (dkD P s₀))) (ekT_eq s₀) htr e0 ht hcT ha hn)
    fun s₁ ⟨mN,fN,e₁,v₁⟩ => ?_)
  have kb₁ := e₁.kb
  have c₁ : bytesAt s₁.mem (sA (deL P) s₀ (CB P)) P.ctLen = cprW P s₀ sB.mem :=
    ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aMW true P (deL P) s₀ sB.mem) (gD P s₀).2 i))
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
  have c₂ : bytesAt s₂.mem (sA (deL P) s₀ (CB P)) P.ctLen = cprW P s₀ sB.mem := by
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
  refine WP.mono (sel_ok hp kb₃ (e := decide (cD P s₀ = cprW P s₀ sB.mem)) (by
    rw [x₃]; by_cases h : cD P s₀ = cprW P s₀ sB.mem <;> simp [h])) fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact safe_R hp (b := 2) ⟨by dek, by dek⟩ (by dek) (.inl (by dek))
  refine WP.mono (epilogue_ok hp kb₄) fun s' ⟨abi, x0, hm⟩ => ⟨abi, ?_, ?_⟩
  · rw [x0, k₄.get .x24, k₃.get .x24, x24₂]
  · rw [hm, b₄, m₃, kp₂, jb₂]
    by_cases h : cD P s₀ = cprW P s₀ sB.mem <;> simp [h]


theorem using_correctW (hash : FixedHash.HashFn) (valid : PrfValidW P (deL P) prf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6
      [⟨.x28,KEM.MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
    (hJ : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 136 0x1f
      [⟨.x25,768*P.k+64,32⟩,⟨.x26,0,P.ctLen⟩] [⟨.x28,KEM.JB,32⟩])
    {s₀ : State} (hp : Pre P (deL P) s₀) (hr : Noise.Room P)
    (hc : Calls P) (tables : Optimized.Tables s₀)
    (depthA : (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P).aarch64Depth≤1)
    (depthB : (Impl.MlKem.AArch64.Paired.matrix P false true).aarch64Depth≤1) :
    WP isa (Impl.MlKem.AArch64.Kem16.decaps hash prf P) s₀ fun t=>
      abiPreserved s₀ t ∧ (decapsAArch64 P).post s₀ t := by
  have scratch0 : Covers [⟨kA s₀ (deL P).sc,P.scl⟩] s₀.wr := by
    have hh := cov_w₀ hp (b:=(deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩
      (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.seq (WP.mono (Optimized.WP.tablesDepth (start_using_ok hash hG hp hc tables.transforms tables.gamma
    tables.gammaRead (Optimized.apart_of_covers tables.gammaApart scratch0)) tables depthA) fun sA ⟨hA,ta⟩=>?_)
  have scratchA : Covers [⟨kA s₀ (deL P).sc,P.scl⟩] sA.wr := by
    have hh := cov_w hp hA.kb (b:=(deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩
      (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  have mt : MatrixTable P (deL P) s₀ sA :=
    ⟨ta.shuffle,ta.shuffleRead,Optimized.apart_of_covers ta.shuffleApart scratchA⟩
  refine WP.seq (WP.mono (Optimized.WP.tablesDepth
    (paired_matrix_ok hp (BInvW.zero (w16 := true) hA.kb hA.x24 hA.rho) mt) ta depthB)
    fun sB ⟨⟨hB,_⟩,tb⟩=>?_)
  refine WP.mono (fused_c_W_ok valid hash hJ hp hr hc hA tb.transforms hB tb.gamma tb.gammaRead
    (readonly_enc hp hB.kb (encArgs hp.wf) tb.gammaApart tb.gammaStack)
    (readonly_noise hp hr hB.kb tb.gammaApart)) fun t ht=>⟨ht.abi,post_ofW hB ht⟩

end VG.Proof.MlKem.AArch64.Decaps
