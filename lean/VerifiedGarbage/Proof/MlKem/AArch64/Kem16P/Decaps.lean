module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Encrypt
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVDecode
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyTransform
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutTables
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.DecapsCmp
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenNoise
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Tail
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Noise
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing

/-! # The decapsulation computing PRF outputs in the matrix is correct

`using_correctDP`: `Kem16P.decaps`: `m'`, `G` and `z ‖ c` copied to
`scratch`, the pairs absorbing `z ‖ c` into the third state, `J(z ‖ c)` to
`JB` (`tailJP_ok`), the pairs and the singleton computing PRF outputs
(`matrixP_ok`), then the re-encryption from their buffers (`encrypt_restP`),
the comparison and the selection (`fused_c_P_ok`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Decaps
open VG.Proof.MlKem.AArch64.Hybrid (Stk128 MT3 HashOk HInvW SrcOk jM jE jM_ok TStk WP.tables128 bW3)
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem

variable {P : KemLay} {prf : Nat→Nat→Prog isa}

/-- What decapsulation keeps through the matrix: `K'`, `r'` and `m'` from the
first phase, and `K̄ = J(z ‖ c)`. -/
structure DOk (P : KemLay) (s₀ : State) (mem : Mem) : Prop where
  kp : bytesAt mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1
  r : bytesAt mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2
  m : bytesAt mem (sA (deL P) s₀ MB) 32 = mD P s₀
  jb : bytesAt mem (sA (deL P) s₀ JB) 32 = jD P s₀

/-- What the matrix writes misses the rest of the first `AH` bytes of `scratch` past the third state. -/
theorem bwp_far {s₀ : State} (hp : Pre P (deL P) s₀) (hk : Stk128 P (deL P) s₀) {o l : Nat}
    (f : o + l ≤ SV P + 48) (h0 : 200 ≤ o) (h1 : o + l ≤ SB + 32 ∨ SB + 34 ≤ o) (h2 : o + l ≤ AH)
    (h3 : o + l ≤ SS ∨ SS + 2048 ≤ o) :
    ∀ r ∈ bWP P (deL P) s₀, (R (kA s₀) (deL P).sc o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp f (by lom) h1
      · exact sdisj hp f (by lom) (.inl h2)
      · exact sdisj hp f (by lom) h3
      · exact below_R hp hp.scb (hp.fs f)
    · rcases mem2' hr with rfl | rfl
      · exact sdisj hp f (by lom) (.inr h0)
      · exact (hk.R hp.scb (hp.fs f)).symm
  · rw [List.mem_singleton.mp hr]; exact sdisj hp f (by lom) (.inl (by lom))

theorem dok_frame {s₀ : State} (hp : Pre P (deL P) s₀) (hk : Stk128 P (deL P) s₀) {m m' : Mem}
    (h : DOk P s₀ m) (hf : Frame (bWP P (deL P) s₀) m m') : DOk P s₀ m' := by
  have hw := hp.wf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bytesAt_frame hf (bwp_far hp hk (o := KP) (l := 32) (by lom) (by decide) (by decide) (by decide)
      (by decide)) (by decide)]
    exact h.kp
  · rw [bytesAt_frame hf (bwp_far hp hk (o := RB) (l := 32) (by lom) (by decide) (by decide) (by decide)
      (by decide)) (by decide)]
    exact h.r
  · rw [bytesAt_frame hf (bwp_far hp hk (o := MB) (l := 32) (by lom) (by decide) (by decide) (by decide)
      (by decide)) (by decide)]
    exact h.m
  · rw [bytesAt_frame hf (bwp_far hp hk (o := JB) (l := 32) (by lom) (by decide) (by decide) (by decide)
      (by decide)) (by decide)]
    exact h.jb

/-- **`J(z ‖ c)`** to `JB` after the pairs absorbing `z ‖ c`, starting the
paired matrix's invariant after it. -/
theorem tailJP_ok {s₀ u : State} (hp : Pre P (deL P) s₀) (hk : Stk128 P (deL P) s₀)
    (ho : HashOk P (Impl.MlKem.AArch64.Kem16.jSrc P)) {mA : Mem} {ρ : List Byte}
    (kp : bytesAt mA (sA (deL P) s₀ KP) 32 = (gD P s₀).1) (r : bytesAt mA (sA (deL P) s₀ RB) 32 = (gD P s₀).2)
    (m : bytesAt mA (sA (deL P) s₀ MB) 32 = mD P s₀)
    (hu : HInvW true P (deL P) (jM P) s₀ mA ρ (jE P s₀)
      (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (jM P).S) (Impl.MlKem.AArch64.Hybrid.hashPairs (jM P).S) u)
    (mu : MT3 P (deL P) s₀ u) :
    WP isa (.block Impl.MlKem.AArch64.Kem16.tailJ) u fun v => DOk P s₀ v.mem ∧
      PInvW true P (deL P) s₀ v.mem ρ (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (jM P).S) 0 v ∧
      MT3 P (deL P) s₀ v := by
  have hw := hp.wf
  have hst := hu.hash
  rw [Hybrid.hstate_done (by
    have h3 : ((32 + P.ctLen) / 136 + 1) % 3 = 0 := ho.three
    have hz : (KPke.dkZ P.params (dkD P s₀)).length = 32 := by
      simp only [KPke.dkZ, List.length_take, List.length_drop, bytesAt_length,
        show P.params.k = P.k from rfl, KemLay.dkLen]
      omega
    simp only [List.length_append, hz, cD, bytesAt_length, Impl.MlKem.AArch64.Hybrid.hashPairs,
      Impl.MlKem.AArch64.Hybrid.blocks, jM, Impl.MlKem.AArch64.Kem16.jSrc]
    omega)] at hst
  refine WP.mono_syms (tailJ_ok hp (by have := ho.pairs; simp only [jM]; omega) hu.b hst)
    fun t ⟨hB₁, _, jb₁, far₁, f₁⟩ sy => ?_
  have b3 : ∀ {o : Nat}, o + 32 ≤ SV P + 48 → 200 ≤ o → (o + 32 ≤ SB + 32 ∨ SB + 34 ≤ o) → o + 32 ≤ AH →
      (o + 32 ≤ SS ∨ SS + 2048 ≤ o) → ∀ r ∈ bW3 P (deL P) s₀, (R (kA s₀) (deL P).sc o 32).Disjoint r :=
    fun f h0 h1 h2 h3 r hr => bwp_far hp hk f h0 h1 h2 h3 r (List.mem_append_left _ hr)
  refine ⟨⟨?_, ?_, ?_, jb₁⟩, ⟨hB₁, Frame.refl _ _, fun N hN => absurd hN (Nat.not_lt_zero _)⟩,
    mu.frame (hB₁.kb.rd.trans hu.b.kb.rd.symm) (hB₁.kb.wr.trans hu.b.kb.wr.symm) sy f₁ fun r hr => .inl ?_⟩
  · rw [far₁ (by lom) (by decide), bytesAt_frame hu.fr (b3 (by lom) (by decide) (by decide) (by decide) (by decide))
      (by decide)]
    exact kp
  · rw [far₁ (by lom) (by decide), bytesAt_frame hu.fr (b3 (by lom) (by decide) (by decide) (by decide) (by decide))
      (by decide)]
    exact r
  · rw [far₁ (by lom) (by decide), bytesAt_frame hu.fr (b3 (by lom) (by decide) (by decide) (by decide) (by decide))
      (by decide)]
    exact m
  · rw [List.mem_singleton.mp hr]; exact scratch_sub hp (by lom)

/-- After the matrix: the re-encryption of `Kem16P.deRestP` from the first `n`
PRF outputs in their buffers (`encrypt_restP`), the comparison and the selection. -/
theorem fused_c_P_ok (valid : PrfValidW P (deL P) prf)
    {s₀ : State} (hp : Pre P (deL P) s₀) (hr : Noise.Room P) (hc : Calls P) {sB : State} {n : Nat}
    (hn : 2 * P.k ≤ n) (htr : Optimized.TransformTables sB)
    (hB : BInvW true P (deL P) s₀ sB.mem (rhoD P s₀) (P.k * P.k) sB) (hd : DOk P s₀ sB.mem)
    (ht : Dot.GammaArtifact sB.mem (sB.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨sB.syms "VG_MLKEM_GAMMA",512⟩] (sB.rd++sB.wr))
    (ha : ∀r∈encW P (deL P) s₀ 3 (CB P), (⟨sB.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn' : ∀ r ∈ noiseW P (deL P) s₀, (⟨sB.syms "VG_MLKEM_GAMMA", 512⟩ : Region).Disjoint r)
    (hprf : ∀ N < min n (Impl.MlKem.AArch64.Kem16P.prfs P), PrfAt P (deL P) s₀ sB.mem sB.mem N) :
    WP isa (Impl.MlKem.AArch64.Kem16P.deRestP prf P n) sB (DoneW P s₀ sB.mem (sB.gpr .x24)) := by
  have hw := hp.wf
  have e0 : EInvW true P (deL P) s₀ 3 (CB P) sB.mem sB.mem (sB.gpr .x24) (gD P s₀).2 (mD P s₀) 0 0 sB :=
    ⟨hB.kb, rfl, hd.r, hd.m, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  -- `c'`
  refine WP.seq (WP.mono (encrypt_restP valid hp hr hc (encArgs hw) hn (T := ekT (KPke.dkEk P.params (dkD P s₀)))
    (ekT_eq s₀) htr e0 ht hcT ha hn' hprf) fun s₁ ⟨mN, fN, e₁, v₁⟩ => ?_)
  have kb₁ := e₁.kb
  have c₁ : bytesAt s₁.mem (sA (deL P) s₀ (CB P)) P.ctLen = cprW P s₀ sB.mem :=
    ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aMW true P (deL P) s₀ sB.mem) (gD P s₀).2 i))
      (fun i hi => by rw [ptr_add]; exact e₁.u i hi) (by rw [ptr_add]; exact v₁)
  have kp₁ : bytesAt s₁.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [bytesAt_frame e₁.fr (far_encW hp (by decide) (by decide) (by decide)) (by decide)]
    rw [bytesAt_frame fN (noiseW_far hp hr (by lom) (.inl (by lom))) (by decide)]
    exact hd.kp
  have jb₁ : bytesAt s₁.mem (sA (deL P) s₀ JB) 32 = jD P s₀ := by
    rw [bytesAt_frame e₁.fr (far_encW hp (by decide) (by decide) (by decide)) (by decide)]
    rw [bytesAt_frame fN (noiseW_far hp hr (by lom) (.inl (by lom))) (by decide)]
    exact hd.jb
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

/-- **The decapsulation computing PRF outputs in the matrix is correct.** -/
theorem using_correctDP (hash : FixedHash.HashFn) (valid : PrfValidW P (deL P) prf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6
      [⟨.x28,KEM.MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
    {s₀ : State} (hp : Pre P (deL P) s₀) (hk : Stk128 P (deL P) s₀)
    (hs : SrcOk (Impl.MlKem.AArch64.Kem16.jSrc P))
    (ho : HashOk P (Impl.MlKem.AArch64.Kem16.jSrc P)) (h8 : 8 * (P.ctLen / 8) = P.ctLen)
    (hr : Noise.Room P) (hc : Calls P) (tables : Optimized.Tables s₀) (ts : TStk s₀)
    (hpl : 2 * P.k ≤ Impl.MlKem.AArch64.Kem16P.placed P
      (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Kem16.jSrc P)))
    (hfin : finalCount P (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Kem16.jSrc P)) =
      Impl.MlKem.AArch64.Kem16P.placed P
        (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Kem16.jSrc P)))
    (depthA : (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P).aarch64Depth≤1)
    (depthM : (Impl.MlKem.AArch64.Kem16P.matrixP P (Impl.MlKem.AArch64.Kem16.jSrc P)
      (.block Impl.MlKem.AArch64.Kem16.tailJ)).aarch64Depth ≤ 8) :
    WP isa (Impl.MlKem.AArch64.Kem16P.decaps hash prf P) s₀ fun t =>
      abiPreserved s₀ t ∧ (decapsAArch64 P).post s₀ t := by
  have hw := hp.wf
  have scratch0 : Covers [⟨kA s₀ (deL P).sc,P.scl⟩] s₀.wr := by
    have hh := cov_w₀ hp (b:=(deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩
      (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.seq (WP.mono_syms (Optimized.WP.tablesDepth (start_using_ok hash hG hp hc tables.transforms tables.gamma
    tables.gammaRead (Optimized.apart_of_covers tables.gammaApart scratch0)) tables depthA) fun uA ⟨hA,ta⟩ syA=>?_)
  have tsA : TStk uA := ts.of syA (by rw [hA.kb.sp])
  refine WP.seq (WP.mono_syms (Optimized.WP.tablesDepth (Hybrid.startJ_ok hp h8 hA) ta (Nat.zero_le _))
    fun sJ ⟨hJ,tj⟩ syJ=>?_)
  have tsJ : TStk sJ := tsA.of syJ (by rw [hJ.a.kb.sp, hA.kb.sp])
  have mt : MT3 P (deL P) s₀ sJ :=
    ⟨Optimized.matrix_table_of_kb hp hJ.a.kb tj, by rw [← hJ.a.kb.sp]; exact tsJ.shuffle⟩
  have h0 : HInvW true P (deL P) (jM P) s₀ sJ.mem (rhoD P s₀) (jE P s₀) 0 0 sJ :=
    ⟨BInvW.zero hJ.a.kb hJ.a.x24 hJ.a.rho, Frame.refl _ _, by rw [Hybrid.hstate_zero]; exact hJ.zero, hJ.msg⟩
  -- The matrix, with `J(z ‖ c)` to `JB` after the pairs absorbing `z ‖ c`.
  refine WP.seq (WP.mono_syms (WP.tables128 (matrixP_ok (M := jM P) hp hk (jM_ok hp hk hs) ho h0 mt
    fun u hu mu _ => tailJP_ok hp hk ho hJ.a.kp hJ.a.r hJ.a.m hu mu) tj tsJ depthM)
    fun uB ⟨⟨mG, gG, hB, _⟩, tb⟩ _ => ?_)
  -- The re-encryption from the buffers, the comparison and the selection.
  have gB : DOk P s₀ uB.mem := dok_frame hp hk gG hB.fr
  have hprf : ∀ N < min (Impl.MlKem.AArch64.Kem16P.placed P
      (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Kem16.jSrc P))) (Impl.MlKem.AArch64.Kem16P.prfs P),
      PrfAt P (deL P) s₀ uB.mem uB.mem N := fun N hN => by
    have pr := hB.prf N (by simp only [jM] at hfin ⊢; rw [hfin]; omega)
    show Noise.Rate128 _ _ _
    rw [seed_mA hp hk hB.fr]
    exact pr
  have hn' : ∀ r ∈ noiseW P (deL P) s₀, (⟨uB.syms "VG_MLKEM_GAMMA", 512⟩ : Region).Disjoint r :=
    fun r hr' => Optimized.apart_of_covers tb.gammaApart fun a n ⟨q, hq, hc⟩ =>
      noiseW_cov hp hr hB.b.kb a n ⟨q, by rw [List.mem_singleton.mp hq]; exact hr', hc⟩
  exact WP.mono (fused_c_P_ok valid hp hr hc hpl tb.transforms hB.b gB tb.gamma tb.gammaRead
    (readonly_enc hp hB.b.kb (encArgs hw) tb.gammaApart tb.gammaStack) hn' hprf)
    fun t ht => ⟨ht.abi, post_ofW hB.b ht⟩

end VG.Proof.MlKem.AArch64.Kem16P
