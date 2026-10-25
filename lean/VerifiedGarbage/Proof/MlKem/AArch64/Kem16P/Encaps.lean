module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Encrypt
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Start
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Tail

/-! # The encapsulation computing PRF outputs in the matrix is correct

`using_correctP`: `Kem16P.encaps`: the pairs hashing `ek`, `G`, the pairs and
the singleton computing PRF outputs (`matrixP_ok`), then the noise from their
buffers, `u` and `v` (`encrypt_restP`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps
open VG.Proof.MlKem.AArch64.Hybrid (Stk128 MT3 HashOk HInvW AfterTN tailHN_ok mb_bW3 ekM SrcOk
  ekM_ok ekM_base TStk WP.tables128 startH_ok)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay} {prf : Nat→Nat→Prog isa}

/-- What `G` leaves: the key, `r` and `m`. -/
def GOk (P : KemLay) (s₀ : State) (m : Mem) : Prop :=
  bytesAt m (kA s₀ 2) 32 = (gE P s₀).1 ∧ bytesAt m (sA (enL P) s₀ RB) 32 = (gE P s₀).2 ∧
  bytesAt m (sA (enL P) s₀ MB) 32 = mE s₀

/-- The key is apart from `scratch`. -/
theorem key_scr {s₀ : State} (hp : Pre P (enL P) s₀) {o l : Nat} (f : o + l ≤ (enL P).len 4) :
    Region.Disjoint ⟨kA s₀ 2, 32⟩ (R (kA s₀) 4 o l) :=
  (hp.args.disj 2 (by enk) 4 (by enk) (by decide) (.inl (by enk))).sub_right (R.sub f)

/-- The key, `r` and `m` are apart from what the matrix writes after `G`. -/
theorem gok_frame {s₀ : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P (enL P) s₀) {m m' : Mem}
    (h : GOk P s₀ m) (hf : Frame (bWP P (enL P) s₀) m m') : GOk P s₀ m' := by
  have hw := hp.wf
  refine ⟨?_, ?_, ?_⟩
  · rw [bytesAt_frame hf (fun r hr => ?_) (by decide)]; exact h.1
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact key_far hp (.inl hr)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact key_scr hp (hp.fs (by lom))
        · exact ((hk.args 2 (by enk)).symm.sub_left (fun _ h => h))
    · rw [List.mem_singleton.mp hr]; exact key_scr hp (hp.fs (by lom))
  · rw [bytesAt_frame hf (r_far hp hk) (by decide)]; exact h.2.1
  · rw [bytesAt_frame hf (fun r hr => ?_) (by decide)]; exact h.2.2
    rcases List.mem_append.mp hr with hr | hr
    · exact mb_bW3 hp hk r hr
    · rw [List.mem_singleton.mp hr]; exact sdisj hp (by lom) (by lom) (by lom)

/-- **`G`** after the pairs hashing `ek`: the key, `r` and `m`, and the paired
matrix's invariant from the memory `G` leaves. -/
theorem gStep_ok (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]
      [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) {s₀ u : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P (enL P) s₀)
    (ho : HashOk P (Impl.MlKem.AArch64.Hybrid.ekSrc P)) (tables : Tables s₀) {mA : Mem} {ρ : List Byte}
    (hmA : bytesAt mA (sA (enL P) s₀ MB) 32 = mE s₀)
    (hu : HInvW true P (enL P) (ekM P) s₀ mA ρ (ekE P s₀)
      (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (ekM P).S) (Impl.MlKem.AArch64.Hybrid.hashPairs (ekM P).S) u)
    (mu : MT3 P (enL P) s₀ u) (su : u.syms = s₀.syms) :
    WP isa (Impl.MlKem.AArch64.Kem16P.gAt hash) u fun v => GOk P s₀ v.mem ∧
      PInvW true P (enL P) s₀ v.mem ρ (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (ekM P).S) 0 v ∧
      MT3 P (enL P) s₀ v := by
  have hw := hp.wf
  have hm : bytesAt u.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame hu.fr (mb_bW3 hp hk) (by decide)]; exact hmA
  have hst := hu.hash
  rw [Hybrid.hstate_done (by
    have h3 : (P.ekLen / 136 + 1) % 3 = 0 := ho.three
    have : (ekE P s₀).length = P.ekLen := bytesAt_length _ _ _
    simp only [Impl.MlKem.AArch64.Hybrid.hashPairs, Impl.MlKem.AArch64.Hybrid.blocks, ekM,
      Impl.MlKem.AArch64.Hybrid.ekSrc]
    omega)] at hst
  refine WP.mono_syms (tailHN_ok hash hG hp (by
      have := ho.pairs
      simp only [ekM]; omega) hu.b hm hst) fun v ⟨hv, fv⟩ sv => ?_
  -- The rejection table is apart from what `G` writes.
  have key : (Region.mk (u.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint
      ⟨kA s₀ ((enL P).slot 1) + BitVec.ofNat 64 0, 32⟩ := by
    rw [su]
    refine apart_of_covers tables.shuffleApart ?_
    have c := cov_w hp hu.b.kb (b := 2) (o := 0) (l := 32) ⟨by enk, by enk⟩ (by enk)
    rw [hu.b.kb.wr] at c
    exact c
  have art : Rej8.TableArtifact v.mem (u.syms "VG_MLKEM_REJ_SHUFFLE") :=
    mu.t.artifact.frame fv fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rw [List.mem_singleton.mp hr]
        exact mu.t.apart.sub_right (scratch_sub hp (o := HB) (l := 32) (by lom))
      · rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
        · exact mu.t.apart.sub_right (scratch_sub hp (o := KEM.ST) (l := 200) (by lom))
        · exact mu.t.apart.sub_right (scratch_sub hp (o := WK) (l := 640) (by lom))
        · exact mu.stk.sub_right (below_sub (by decide) (by decide))
        · exact key
        · exact mu.t.apart.sub_right (scratch_sub hp (o := RB) (l := 32) (by lom))
  exact ⟨⟨hv.key, hv.r, hv.m⟩, ⟨hv.b, Frame.refl _ _, fun N hN => absurd hN (Nat.not_lt_zero _)⟩,
    ⟨by rw [sv]; exact art, by rw [sv, hv.b.kb.rd, hv.b.kb.wr, ← hu.b.kb.rd, ← hu.b.kb.wr]; exact mu.t.readable,
      by rw [sv]; exact mu.t.apart⟩, by rw [sv]; exact mu.stk⟩

/-- **The encapsulation computing PRF outputs in the matrix is correct.** -/
theorem using_correctP (hash : FixedHash.HashFn) (valid : PrfValidW P (enL P) prf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]
      [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) {s₀ : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P (enL P) s₀)
    (hs : SrcOk (Impl.MlKem.AArch64.Hybrid.ekSrc P))
    (ho : HashOk P (Impl.MlKem.AArch64.Hybrid.ekSrc P)) (hr : Noise.Room P) (hc : Calls P) (tables : Tables s₀)
    (ts : TStk s₀)
    (hpl : 2 * P.k ≤ Impl.MlKem.AArch64.Kem16P.placed P
      (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Hybrid.ekSrc P)))
    (hfin : finalCount P (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Hybrid.ekSrc P)) =
      Impl.MlKem.AArch64.Kem16P.placed P
        (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Hybrid.ekSrc P)))
    (depthM : (Impl.MlKem.AArch64.Kem16P.matrixP P (Impl.MlKem.AArch64.Hybrid.ekSrc P)
      (Impl.MlKem.AArch64.Kem16P.gAt hash)).aarch64Depth ≤ 8) :
    WP isa (Impl.MlKem.AArch64.Kem16P.encaps hash prf P) s₀ fun t =>
      abiPreserved s₀ t ∧ (encapsAArch64 P).post s₀ t := by
  have hw := hp.wf
  refine WP.seq (WP.mono_syms (WP.tablesDepth (startH_ok hp) tables
    (by unfold Impl.MlKem.AArch64.Hybrid.startH; exact Nat.zero_le _)) fun uA ⟨hA, ta⟩ syA => ?_)
  have tsA : TStk uA := ts.of syA (by rw [hA.kb.sp])
  have mt : MT3 P (enL P) s₀ uA := ⟨matrix_table_of_kb hp hA.kb ta, by rw [← hA.kb.sp]; exact tsA.shuffle⟩
  have h0 : HInvW true P (enL P) (ekM P) s₀ uA.mem (rhoE P s₀) (ekE P s₀) 0 0 uA :=
    ⟨BInvW.zero hA.kb hA.x24 hA.rho, Frame.refl _ _, by rw [Hybrid.hstate_zero]; exact hA.zero,
      by rw [ekM_base]; exact hA.kb.ro 0 (show 0 < 2 by decide)⟩
  -- The matrix, with `G` after the pairs hashing `ek`.
  refine WP.seq (WP.mono_syms (WP.tables128 (matrixP_ok (M := ekM P) hp hk (ekM_ok hp hk hs) ho h0 mt
    fun u hu mu su => gStep_ok hash hG hp hk ho tables hA.m hu mu (su.trans syA))
    ta tsA depthM) fun uB ⟨⟨mG, gG, hB, _⟩, tb⟩ _ => ?_)
  -- The noise, `u`, `v` and the epilogue.
  have gB : GOk P s₀ uB.mem := gok_frame hp hk gG hB.fr
  have e0 : EInvW true P (enL P) s₀ 2 0 uB.mem uB.mem (uB.gpr .x24) (gE P s₀).2 (mE s₀) 0 0 uB :=
    ⟨hB.b.kb, rfl, gB.2.1, gB.2.2, fun i hi j hj => ⟨hB.b.reduced hi hj, rfl⟩,
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  have hprf : ∀ N < min (Impl.MlKem.AArch64.Kem16P.placed P
      (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Hybrid.ekSrc P))) (Impl.MlKem.AArch64.Kem16P.prfs P),
      PrfAt P (enL P) s₀ uB.mem uB.mem N := fun N hN => by
    have pr := hB.prf N (by simp only [ekM] at hfin ⊢; rw [hfin]; omega)
    show Noise.Rate128 _ _ _
    rw [seed_mA hp hk hB.fr]
    exact pr
  have hn' : ∀ r ∈ noiseW P (enL P) s₀, (⟨uB.syms "VG_MLKEM_GAMMA", 512⟩ : Region).Disjoint r :=
    fun r hr' => apart_of_covers tb.gammaApart fun a n ⟨q, hq, hc⟩ =>
      noiseW_cov hp hr hB.b.kb a n ⟨q, by rw [List.mem_singleton.mp hq]; exact hr', hc⟩
  refine WP.seq (WP.mono (encrypt_restP valid hp hr hc encArgs hpl (T := ekT (ekE P s₀)) (ekT_eq s₀)
    tb.transforms e0 tb.gamma tb.gammaRead (readonly_enc hp hB.b.kb encArgs tb.gammaApart tb.gammaStack) hn' hprf)
    fun s₁ ⟨mN, fN, e₁, v₁⟩ => ?_)
  refine WP.mono (epilogue_ok hp e₁.kb) fun s' ⟨abi, x0, hm⟩ => ⟨abi, post_ofW hB.b ⟨abi, by rw [x0, e₁.x24], ?_, ?_⟩⟩
  · rw [hm, bytesAt_frame e₁.fr (fun r hh => key_far hp (.inr hh)) (by decide)]
    have hw := hp.wf
    rw [bytesAt_frame fN (fun r hr' => ?_) (by decide)]
    · exact gB.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact key_scr hp (hp.fs (by lom))
    · exact key_scr hp (hp.fs (by lom))
    · refine key_scr hp ?_
      show _ ≤ P.scl
      have := Noise.noise_fits (P := P) hr (i := P.k - 1) (by have := hw.facts; omega)
      simp only [Impl.MlKem.AArch64.Noise.noiseOff] at this ⊢; have := hw.facts; omega
  · rw [hm]
    exact ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aMW true P (enL P) s₀ uB.mem) (gE P s₀).2 i))
      (fun i hi => by have := e₁.u i hi; rwa [Nat.zero_add] at this) (by rwa [Nat.zero_add] at v₁)

end VG.Proof.MlKem.AArch64.Kem16P
