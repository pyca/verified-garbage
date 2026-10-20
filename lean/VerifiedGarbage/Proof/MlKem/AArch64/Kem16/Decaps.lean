module
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encrypt
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVDecode
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVInv
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyTransform
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutTables
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.DecapsStart
import VerifiedGarbage.Proof.MlKem.AArch64.DecapsCmp
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenNoise
import VerifiedGarbage.Proof.Framework.Block

/-! # The 16-bit decapsulation is correct

`fused_c_W_ok`: the re-encryption of `Kem16.deRest` (`encrypt_restW`), the
comparison and the selection; `using_correctW`: `Kem16.decaps`: `m'`, `G` and
`ρ`, `z ‖ c` copied to `scratch` (`startJ_ok`), the matrix sampled with 16
bits while its first pairs absorb `z ‖ c` into the third state
(`Hybrid.matrixH_ok`), `J(z ‖ c)` from that state to `JB`, then the rest. -/

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

/-- `BInvW` carried over writes apart from `ρ` and `Â`, from the memory written. -/
theorem binv_move {w16 : Bool} {L : Layout} {s₀ s t : State} {mA : Mem} {ρ : List Byte} {n : Nat}
    (h : BInvW w16 P L s₀ mA ρ n s) (hk : KB P L s₀ t) (h24 : t.gpr .x24 = s.gpr .x24) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hρ : ∀ r ∈ rs, (R (kA s₀) L.sc SB 32).Disjoint r)
    (hA : ∀ e < n, ∀ r ∈ rs, (polyRegion (aP L s₀ e)).Disjoint r) : BInvW w16 P L s₀ t.mem ρ n t := by
  refine ⟨hk, Frame.refl _ _, ?_, by rw [h24]; exact h.acc, fun e he => reducedW_frame hf (hA e he) (h.red e he),
    fun e he => ?_⟩
  · rw [bytesAt_frame hf hρ (by decide)]; exact h.rho
  · rw [polyAtW_frame hf (hA e he)]; exact h.res e he

/-- After `K̄ = J(z ‖ c)` to `JB`: the 16-bit re-encryption of `Kem16.deRest`
(`encrypt_restW`), the comparison and the selection. -/
theorem fused_c_W_ok (valid : PrfValidW P (deL P) prf)
    {s₀ : State} (hp : Pre P (deL P) s₀) (hr : Noise.Room P) (hc : Calls P) {sB : State}
    (htr : Optimized.TransformTables sB)
    (hB : BInvW true P (deL P) s₀ sB.mem (rhoD P s₀) (P.k * P.k) sB)
    (r₀ : bytesAt sB.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2)
    (m₀ : bytesAt sB.mem (sA (deL P) s₀ MB) 32 = mD P s₀)
    (kp₀ : bytesAt sB.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1)
    (jb₀ : bytesAt sB.mem (sA (deL P) s₀ JB) 32 = jD P s₀)
    (ht : Dot.GammaArtifact sB.mem (sB.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨sB.syms "VG_MLKEM_GAMMA",512⟩] (sB.rd++sB.wr))
    (ha : ∀r∈encW P (deL P) s₀ 3 (CB P), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn : ∀r∈Noise.allWrites P false (kA s₀ (deL P).sc), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Kem16.deRest prf P) sB (DoneW P s₀ sB.mem (sB.gpr .x24)) := by
  have hw := hp.wf
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
  have hroom := hr.kem
  have kp₁ : bytesAt s₁.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [bytesAt_frame e₁.fr (far_encW hp (by decide) (by decide) (by decide)) (by decide)]
    rw [bytesAt_frame fN (Kem.noise_far hp hr hp.scb (hp.fs (by lom)) (.inr (by lom))) (by decide)]
    exact kp₀
  have jb₁ : bytesAt s₁.mem (sA (deL P) s₀ JB) 32 = jD P s₀ := by
    rw [bytesAt_frame e₁.fr (far_encW hp (by decide) (by decide) (by decide)) (by decide)]
    rw [bytesAt_frame fN (Kem.noise_far hp hr hp.scb (hp.fs (by lom)) (.inr (by lom))) (by decide)]
    exact jb₀
  have x24₁ : s₁.gpr .x24 = sB.gpr .x24 := e₁.x24
  -- `c = c'`
  refine WP.seq (WP.mono (cmp_ok hp kb₁ c₁) fun s₃ ⟨k₃, m₃, x₃⟩ => ?_)
  have kb₃ := kb₁.block k₃ m₃ (by decide)
  -- the key
  change WP isa (.block (deSel ++ P.kemEpilogue)) s₃ _
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok hp kb₃ (e := decide (cD P s₀ = cprW P s₀ sB.mem)) (by
    rw [x₃]; by_cases h : cD P s₀ = cprW P s₀ sB.mem <;> simp [h])) fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact safe_R hp (b := 2) ⟨by dek, by dek⟩ (by dek) (.inl (by dek))
  refine WP.mono (epilogue_ok hp kb₄) fun s' ⟨abi, x0, hm⟩ => ⟨abi, ?_, ?_⟩
  · rw [x0, k₄.get .x24, k₃.get .x24, x24₁]
  · rw [hm, b₄, m₃, kp₁, jb₁]
    by_cases h : cD P s₀ = cprW P s₀ sB.mem <;> simp [h]

/-- `J(z ‖ c)`, the first 32 bytes of the third state, to `JB` (`Kem16.tailJ`). -/
theorem tailJ_ok {s₀ sB : State} (hp : Pre P (deL P) s₀)
    (hB : BInvW true P (deL P) s₀ sB.mem (rhoD P s₀) (P.k * P.k) sB)
    (hst : Spec.Sha3.stateAt sB.mem (kA s₀ (deL P).sc) =
      Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 0x1f) (Hybrid.jE P s₀))) :
    WP isa (.block Impl.MlKem.AArch64.Kem16.tailJ) sB fun t =>
      BInvW true P (deL P) s₀ t.mem (rhoD P s₀) (P.k * P.k) t ∧ t.gpr .x24 = sB.gpr .x24 ∧
      bytesAt t.mem (sA (deL P) s₀ JB) 32 = jD P s₀ ∧
      ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ JB ∨ JB + 32 ≤ o) →
        bytesAt t.mem (sA (deL P) s₀ o) l = bytesAt sB.mem (sA (deL P) s₀ o) l := by
  have hw := hp.wf
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 3) (D := kA s₀ 3) (so := KEM.ST) (dO := JB)
    (by decide) (by decide) (by decide) (by decide) (sdisj hp (by lom) (by lom) (by lom))
    hB.kb.x28 hB.kb.x28 (cov_sr hp hB.kb (by lom)) (cov_s hp hB.kb (by lom))) fun t ⟨k, f, b⟩ => ?_
  have kb := hB.kb.frame k f (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  have far : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ JB ∨ JB + 32 ≤ o) →
      bytesAt t.mem (sA (deL P) s₀ o) l = bytesAt sB.mem (sA (deL P) s₀ o) l := fun hf h => by
    refine bytesAt_frame f (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]; exact sdisj hp hf (by lom) h
  refine ⟨binv_move hB kb (k.get .x24) f (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact sdisj hp (by lom) (by lom) (by lom))
    (fun e he r hr => by
      rw [List.mem_singleton.mp hr]
      exact sdisj hp (o₁ := AH + 1024 * e) (l₁ := 1024) (by lom) (by lom) (.inr (by lom))),
    k.get .x24, ?_, far⟩
  rw [show sA (deL P) s₀ JB = kA s₀ 3 + BitVec.ofNat 64 JB from rfl, b,
    show KEM.ST = 0 from rfl, ptr_zero]
  show _ = J (Hybrid.jE P s₀)
  rw [J_eq, Hybrid.bytesAt_squeeze]
  show Spec.Sha3.squeezeFrom 136 (Spec.Sha3.stateAt sB.mem (kA s₀ (deL P).sc)) 0 32 = _
  rw [hst]; rfl

/-- The first phase and `z ‖ c` copied to `scratch`, with what the matrix needs. -/
theorem prefixJ (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6
      [⟨.x28,KEM.MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
    {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) (h8 : 8 * (P.ctLen / 8) = P.ctLen)
    (tables : Optimized.Tables s₀) (ts : Hybrid.TStk s₀)
    (depthA : (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P).aarch64Depth≤1) :
    WP isa (.seq (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P)
      (.block (Impl.MlKem.AArch64.Kem16.startJ P))) s₀ fun t =>
      Hybrid.HInvW true P (deL P) (Hybrid.jM P) s₀ t.mem (rhoD P s₀) (Hybrid.jE P s₀) 0 0 t ∧
        Hybrid.MT3 P (deL P) s₀ t := by
  have hw := hp.wf
  have scratch0 : Covers [⟨kA s₀ (deL P).sc,P.scl⟩] s₀.wr := by
    have hh := cov_w₀ hp (b:=(deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩
      (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.seq (WP.mono_syms (Optimized.WP.tablesDepth (start_using_ok hash hG hp hc tables.transforms tables.gamma
    tables.gammaRead (Optimized.apart_of_covers tables.gammaApart scratch0)) tables depthA) fun uA ⟨hA,ta⟩ syA=>?_)
  have tsA : Hybrid.TStk uA := ts.of syA (by rw [hA.kb.sp])
  refine WP.mono_syms (Optimized.WP.tablesDepth (Hybrid.startJ_ok hp h8 hA) ta (Nat.zero_le _))
    fun sJ ⟨hJ,tj⟩ syJ=>?_
  have tsJ : Hybrid.TStk sJ := tsA.of syJ (by rw [hJ.a.kb.sp, hA.kb.sp])
  exact ⟨⟨BInvW.zero hJ.a.kb hJ.a.x24 hJ.a.rho, Frame.refl _ _, by rw [Hybrid.hstate_zero]; exact hJ.zero,
    hJ.msg⟩, Optimized.matrix_table_of_kb hp hJ.a.kb tj, by rw [← hJ.a.kb.sp]; exact tsJ.shuffle⟩

theorem using_correctW (hash : FixedHash.HashFn) (valid : PrfValidW P (deL P) prf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6
      [⟨.x28,KEM.MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
    {s₀ : State} (hp : Pre P (deL P) s₀) (hk : Hybrid.Stk128 P (deL P) s₀)
    (hs : Hybrid.SrcOk (Impl.MlKem.AArch64.Kem16.jSrc P))
    (ho : Hybrid.HashOk P (Impl.MlKem.AArch64.Kem16.jSrc P)) (h8 : 8 * (P.ctLen / 8) = P.ctLen)
    (hr : Noise.Room P) (hc : Calls P) (tables : Optimized.Tables s₀) (ts : Hybrid.TStk s₀)
    (depthA : (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P).aarch64Depth≤1)
    (depthB : (Impl.MlKem.AArch64.Hybrid.matrixH P (Impl.MlKem.AArch64.Kem16.jSrc P) true).aarch64Depth≤8) :
    WP isa (Impl.MlKem.AArch64.Kem16.decaps hash prf P) s₀ fun t=>
      abiPreserved s₀ t ∧ (decapsAArch64 P).post s₀ t := by
  have hw := hp.wf
  have scratch0 : Covers [⟨kA s₀ (deL P).sc,P.scl⟩] s₀.wr := by
    have hh := cov_w₀ hp (b:=(deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩
      (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.seq (WP.mono_syms (Optimized.WP.tablesDepth (start_using_ok hash hG hp hc tables.transforms tables.gamma
    tables.gammaRead (Optimized.apart_of_covers tables.gammaApart scratch0)) tables depthA) fun uA ⟨hA,ta⟩ syA=>?_)
  have tsA : Hybrid.TStk uA := ts.of syA (by rw [hA.kb.sp])
  refine WP.seq (WP.mono_syms (Optimized.WP.tablesDepth (Hybrid.startJ_ok hp h8 hA) ta (Nat.zero_le _))
    fun sJ ⟨hJ,tj⟩ syJ=>?_)
  have tsJ : Hybrid.TStk sJ := tsA.of syJ (by rw [hJ.a.kb.sp, hA.kb.sp])
  have mt : Hybrid.MT3 P (deL P) s₀ sJ :=
    ⟨Optimized.matrix_table_of_kb hp hJ.a.kb tj, by rw [← hJ.a.kb.sp]; exact tsJ.shuffle⟩
  have h0 : Hybrid.HInvW true P (deL P) (Hybrid.jM P) s₀ sJ.mem (rhoD P s₀) (Hybrid.jE P s₀) 0 0 sJ :=
    ⟨BInvW.zero hJ.a.kb hJ.a.x24 hJ.a.rho, Frame.refl _ _, by rw [Hybrid.hstate_zero]; exact hJ.zero, hJ.msg⟩
  refine WP.seq (WP.mono_syms (Hybrid.WP.tables128 (Hybrid.matrixH_ok hp hk (Hybrid.jM_ok hp hk hs) ho h0 mt)
    tj tsJ depthB) fun sB ⟨⟨hB, _⟩, tb⟩ _ => ?_)
  have fbw3 : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 200 ≤ o → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) →
      o + l ≤ AH → (o + l ≤ SS ∨ SS + 2048 ≤ o) →
      ∀ r ∈ Hybrid.bW3 P (deL P) s₀, (R (kA s₀) (deL P).sc o l).Disjoint r := fun f h0' h1 h2 h3 r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp f (by lom) h1
      · exact sdisj hp f (by lom) (.inl h2)
      · exact sdisj hp f (by lom) h3
      · exact below_R hp hp.scb (hp.fs f)
    · rcases mem2' hr with rfl | rfl
      · exact sdisj hp f (by lom) (.inr h0')
      · exact (hk.R hp.scb (hp.fs f)).symm
  have keepB : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 200 ≤ o → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) →
      o + l ≤ AH → (o + l ≤ SS ∨ SS + 2048 ≤ o) →
      bytesAt sB.mem (sA (deL P) s₀ o) l = bytesAt sJ.mem (sA (deL P) s₀ o) l := fun f h0' h1 h2 h3 => by
    rw [bytesAt_frame hB.fr (fbw3 f h0' h1 h2 h3) (by lom)]
  have hst := hB.hash
  rw [Hybrid.hstate_done (by
    have h3 : ((32 + P.ctLen) / 136 + 1) % 3 = 0 := ho.three
    have hz : (KPke.dkZ P.params (dkD P s₀)).length = 32 := by
      simp only [KPke.dkZ, List.length_take, List.length_drop, bytesAt_length,
        show P.params.k = P.k from rfl, KemLay.dkLen]
      omega
    simp only [List.length_append, hz, cD, bytesAt_length, Impl.MlKem.AArch64.Hybrid.hashPairs,
      Impl.MlKem.AArch64.Hybrid.blocks, Hybrid.jM, Impl.MlKem.AArch64.Kem16.jSrc]
    omega)] at hst
  refine WP.seq (WP.mono (Optimized.WP.tablesDepth (tailJ_ok hp hB.b hst) tb (Nat.zero_le _))
    fun s₁ ⟨⟨hB₁, x₁, jb₁, far₁⟩, t₁⟩ => ?_)
  have kp₁ : bytesAt s₁.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [far₁ (by lom) (by decide), keepB (by lom) (by decide) (by decide) (by decide) (by decide)]
    exact hJ.a.kp
  have r₁ : bytesAt s₁.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2 := by
    rw [far₁ (by lom) (by decide), keepB (by lom) (by decide) (by decide) (by decide) (by decide)]
    exact hJ.a.r
  have m₁ : bytesAt s₁.mem (sA (deL P) s₀ MB) 32 = mD P s₀ := by
    rw [far₁ (by lom) (by decide), keepB (by lom) (by decide) (by decide) (by decide) (by decide)]
    exact hJ.a.m
  refine WP.mono (fused_c_W_ok valid hp hr hc t₁.transforms hB₁ r₁ m₁ kp₁ jb₁ t₁.gamma t₁.gammaRead
    (readonly_enc hp hB₁.kb (encArgs hp.wf) t₁.gammaApart t₁.gammaStack)
    (readonly_noise hp hr hB₁.kb t₁.gammaApart)) fun t ht => ⟨ht.abi, post_ofW hB₁ ht⟩

end VG.Proof.MlKem.AArch64.Decaps
