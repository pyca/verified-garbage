module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Final
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Final
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
meta import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.MatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Start
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
import Mathlib.Data.Nat.Cast.Order.Ring
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Encrypt
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Matrix
import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Impl.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState
public import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.MatrixTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Start
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
meta import Mathlib.Data.Nat.Cast.Order.Ring
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Encrypt
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
meta import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Matrix
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
meta import Mathlib.Tactic.IntervalCases
meta import VerifiedGarbage.Impl.MlKem.AArch64.Lay
meta import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState
meta import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
meta import VerifiedGarbage.Proof.MlKem.AArch64.Lay
meta import VerifiedGarbage.TCB.Artifact

/-! ### `MlKem.AArch64.Kem16P.EncapsTop`, which only this module used -/

section

/-! ### `MlKem.AArch64.Kem16P.Encaps`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Kem16.Encaps`, which this module and modules that import it used -/

section

/-! # The 16-bit hashing encapsulation's postcondition

`DoneW` and `post_ofW`: what the noise, `u`, `v` and the epilogue leave, and
the encapsulation's postcondition from it (for `Kem16P/Encaps.lean`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Encaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem
variable {P : KemLay}

/-- What the function leaves, with `Â` stored with 16 bits. -/
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

end

end

/-! # The encapsulation computing PRF outputs in the matrix is correct

`using_correctP`: `Kem16P.encaps`: the pairs hashing `ek`, `G`, the pairs and
the singleton computing PRF outputs (`matrixP_ok`), then the noise from their
buffers, `u` and `v` (`encrypt_restP`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P
variable {sha3 : Bool}

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
    omega_using [h3, this])] at hst
  refine WP.mono_syms (tailHN_ok hash hG hp (by
      have := ho.pairs
      simp only [ekM]; omega_using [this]) hu.b hm hst) fun v ⟨hv, fv⟩ sv => ?_
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
    (depthM : (Impl.MlKem.AArch64.Kem16P.matrixP sha3 P (Impl.MlKem.AArch64.Hybrid.ekSrc P)
      (Impl.MlKem.AArch64.Kem16P.gAt hash)).aarch64Depth ≤ 8) :
    WP isa (Impl.MlKem.AArch64.Kem16P.encaps sha3 hash prf P) s₀ fun t =>
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
  refine WP.seq (WP.mono_syms (WP.tables128 (matrixP_ok (sha3 := sha3) (M := ekM P) hp hk (ekM_ok hp hk hs) ho h0 mt
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
    have pr := hB.prf N (by simp only [ekM] at hfin ⊢; rw [hfin]; omega_using [hN])
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
      have := Noise.noise_fits (P := P) hr (i := P.k - 1) (by have := hw.facts; omega_using [this])
      simp only [Impl.MlKem.AArch64.Noise.noiseOff] at this ⊢; have := hw.facts; omega_arith
  · rw [hm]
    exact ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aMW true P (enL P) s₀ uB.mem) (gE P s₀).2 i))
      (fun i hi => by have := e₁.u i hi; rwa [Nat.zero_add] at this) (by rwa [Nat.zero_add] at v₁)

end VG.Proof.MlKem.AArch64.Kem16P

end

end

/-! # The encapsulation computing PRF outputs in the matrix is constant time

`encapsP_ct`: `Kem16P.encaps` is constant time: the first phase, `G` and the
rest by the taint analyses, the matrix around `G` by `matrixP_relCT`. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps (enL ekE rhoE mE)
open VG.Proof.MlKem.AArch64.Hybrid (Stk128 MT3 HInvW HashOk SrcOk Same ekM ekM_ok ekM_base TStk
  encapsAArch64S entryContractS preS entryS_tables entryS_symbols startH_ok)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {P : KemLay}

/-- The first phase, with what the matrix and `G` need. -/
theorem prefixP {s₀ : State} (hp : Pre P (enL P) s₀) (tables : Tables s₀) (ts : TStk s₀) :
    WP isa (Impl.MlKem.AArch64.Hybrid.startH P) s₀ fun t =>
      HInvW true P (enL P) (ekM P) s₀ t.mem (rhoE P s₀) (ekE P s₀) 0 0 t ∧ MT3 P (enL P) s₀ t ∧
      bytesAt t.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
  refine WP.mono_syms (WP.tablesDepth (startH_ok hp) tables
    (by unfold Impl.MlKem.AArch64.Hybrid.startH; exact Nat.zero_le _)) fun t ⟨hA, ta⟩ sy => ?_
  have tsA : TStk t := ts.of sy (by rw [hA.kb.sp])
  exact ⟨⟨BInvW.zero hA.kb hA.x24 hA.rho, Frame.refl _ _, by rw [Hybrid.hstate_zero]; exact hA.zero,
      by rw [ekM_base]; exact hA.kb.ro 0 (show 0 < 2 by decide)⟩,
    ⟨matrix_table_of_kb hp hA.kb ta, by rw [← hA.kb.sp]; exact tsA.shuffle⟩, hA.m⟩

/-- **The encapsulation computing PRF outputs in the matrix is constant time.** -/
theorem encapsP_ct (hash : FixedHash.HashFn) (prf : Nat → Nat → Prog isa) (hw : P.Wf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]
      [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩])
    (hsrc : SrcOk (Impl.MlKem.AArch64.Hybrid.ekSrc P)) (ho : HashOk P (Impl.MlKem.AArch64.Hybrid.ekSrc P))
    (habs : ∀ blk, 136 * blk < (Impl.MlKem.AArch64.Hybrid.ekSrc P).len → ∃ h,
      (taint.check (Taint.ofRegs [(Impl.MlKem.AArch64.Hybrid.ekSrc P).r, .x28])
        (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock (Impl.MlKem.AArch64.Hybrid.ekSrc P) blk)) h).isSome = true)
    (ha : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4])
      (Impl.MlKem.AArch64.Hybrid.startH P) h).isSome = true)
    (hg : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Kem16P.gAt hash) h).isSome = true)
    (hc : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (.seq (Impl.MlKem.AArch64.Kem16P.encryptRestP prf P
        (Impl.MlKem.AArch64.Kem16P.placed P (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Hybrid.ekSrc P)))
        .x25 0 .x28 MB .x27 0) (.block P.kemEpilogue)) h).isSome = true) :
    ConstantTime isa (entryContractS (encapsAArch64S P)).pre (entryContractS (encapsAArch64S P)).pub
      (Impl.MlKem.AArch64.Kem16P.encaps sha3 hash prf P) := by
  intro s u tr ur t v hs hu hpub et eu
  have ss := preS hs.1
  have su := preS hu.1
  have ps := kem_unstrip (Encaps.pre_of hw ss.1)
  have pu := kem_unstrip (Encaps.pre_of hw su.1)
  have rs : ∀ r ∈ [Reg.x0,.x1,.x2,.x3,.x4], s.gpr r = u.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hpub.1.1
    · exact hpub.1.2.1
    · exact hpub.1.2.2.1
    · exact hpub.1.2.2.2.1
    · exact hpub.1.2.2.2.2.1
  have ptr : ∀ i < 4, kA s ((enL P).slot i) = kA u ((enL P).slot i) := by
    intro i hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      exact rs _ (by simp [enL, argReg])
  have sp : s.sp = u.sp := hpub.1.2.2.2.2.2.1
  have rho : rhoE P s = rhoE P u := map_toNat_inj hpub.1.2.2.2.2.2.2
  have sym := entryS_symbols hpub
  have sm : Same (enL P) (ekM P) s u := ⟨ptr 3 (by decide), by rw [ekM_base, ekM_base]; exact ptr 0 (by decide), sp⟩
  have ts := entryS_tables hs
  have tu := entryS_tables hu
  have ks : Stk128 P (enL P) s := ⟨ss.2.sp, ss.2.args⟩
  have ku : Stk128 P (enL P) u := ⟨su.2.sp, su.2.args⟩
  have ac := VectorTaint.relRegs [.x0,.x1,.x2,.x3,.x4]
    (P := fun a b => a = s ∧ b = u) (fun a b ⟨ha, hb⟩ => by subst a; subst b; exact ⟨sp, rs⟩) ha.choose_spec
  -- Pointers both runs agree on.
  have regs : ∀ {a b : State}, KB P (enL P) s a → KB P (enL P) u b →
      ∀ r ∈ [Reg.x25,.x26,.x27,.x28], a.gpr r = b.gpr r := by
    intro a b ha hb r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · rw [ha.x25, hb.x25, ptr 0 (by decide)]
    · rw [ha.x26, hb.x26, ptr 1 (by decide)]
    · rw [ha.x27, hb.x27, ptr 2 (by decide)]
    · rw [ha.x28, hb.x28, ptr 3 (by decide)]
  -- The first phase.
  obtain ⟨sA, ta, tb, rfl, ea, eb⟩ := Paired.seq_parts et
  obtain ⟨uA, ua, ub, rfl, fa, fb⟩ := Paired.seq_parts eu
  have aeq := (ac _ _ _ _ _ _ ⟨rfl, rfl⟩ ea fa).1
  have hsA := Paired.exec_post (prefixP ps ts.1 ts.2) ea
  have huA := Paired.exec_post (prefixP pu tu.1 tu.2) fa
  rw [← rho] at huA
  -- `G`, between the pairs hashing `ek` and those computing PRF outputs.
  have between : RelCT isa (fun a b => Hybrid.HRel true P (enL P) (ekM P) s u sA.mem uA.mem (rhoE P s)
      (ekE P s) (ekE P u) (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (ekM P).S)
      (Impl.MlKem.AArch64.Hybrid.hashPairs (ekM P).S) a b ∧ a.syms = sA.syms ∧ b.syms = uA.syms)
      (Impl.MlKem.AArch64.Kem16P.gAt hash)
      (PRel P (enL P) s u (rhoE P s) (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (ekM P).S) 0) := by
    intro a b tr' ur' a' b' h ea' eb'
    have ga := Paired.exec_post (gStep_ok hash hG ps ks ho ts.1 hsA.2.2 h.1.1 h.1.2.2.1
      (h.2.1.trans (Exec.syms ea))) ea'
    have gb := Paired.exec_post (gStep_ok hash hG pu ku ho tu.1 huA.2.2 h.1.2.1 h.1.2.2.2.1
      (h.2.2.trans (Exec.syms fa))) eb'
    refine ⟨symbol_taint [.x25,.x26,.x27,.x28] (by rw [h.1.1.b.kb.sp, h.1.2.1.b.kb.sp, sm.sp])
      (regs h.1.1.b.kb h.1.2.1.b.kb)
      (fun name hn => by rw [h.2.1, h.2.2, Exec.syms ea, Exec.syms fa]; exact sym.2 name hn) hg ea' eb',
      ⟨_, ga.2.1⟩, ⟨_, gb.2.1⟩, ga.2.2, gb.2.2, ?_⟩
    rw [Exec.syms ea', Exec.syms eb']; exact h.1.2.2.2.2
  -- The matrix.
  obtain ⟨sB, tc, td, rfl, ec, ed⟩ := Paired.seq_parts eb
  obtain ⟨uB, uc, ud, rfl, fc, fd⟩ := Paired.seq_parts fb
  have bm := matrixP_relCT (sha3 := sha3) ps pu ks ku (ekM_ok ps ks hsrc) (ekM_ok pu ku hsrc) sm ho habs between
    _ _ _ _ _ _ ⟨⟨hsA.1, huA.1, hsA.2.1, huA.2.1, by rw [Exec.syms ea, Exec.syms fa]; exact sym.1⟩, rfl, rfl⟩ ec fc
  obtain ⟨⟨_, bs⟩, ⟨_, bu⟩, _⟩ := bm.2
  -- The rest.
  have ceq := symbol_taint [.x25,.x26,.x27,.x28] (by rw [bs.b.kb.sp, bu.b.kb.sp, sm.sp]) (regs bs.b.kb bu.b.kb)
    (fun name hn => by rw [Exec.syms ec, Exec.syms fc, Exec.syms ea, Exec.syms fa]; exact sym.2 name hn) hc ed fd
  exact by rw [aeq, bm.1, ceq]

end VG.Proof.MlKem.AArch64.Kem16P

end

end

/-!
# `vg_mlkem768_encaps` and `vg_mlkem1024_encaps` computing PRF outputs in the matrix

The instances of `using_correctP` and `encapsP_ct` for ML-KEM-768 and
ML-KEM-1024, with the taint analyses of `G` and of the rest of the code
decided on each, and their contract (`Hybrid/Final.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (encapsAArch64S entryContractS preS entryS_tables srcOk768 srcOk1024
  hashOk768 hashOk1024 habs768 habs1024 startH768_taint startH1024_taint encapsH768Contract encapsH1024Contract
  encapsH768_entry encapsH768_post encapsH768_pub encapsH768_sat encapsH1024_entry encapsH1024_post
  encapsH1024_pub encapsH1024_sat)
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash hole prfW prfW_valid enG768_correct enG1024_correct symSums)
open VG.Proof.MlKem

theorem g_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash c)) h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem restP768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (.seq (Impl.MlKem.AArch64.Kem16P.encryptRestP (prfW c) lay768
        (Impl.MlKem.AArch64.Kem16P.placed lay768 (Impl.MlKem.AArch64.Hybrid.hashPairs
          (Impl.MlKem.AArch64.Hybrid.ekSrc lay768))) .x25 0 .x28 KEM.MB .x27 0)
        (.block lay768.kemEpilogue)) h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem restP1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (.seq (Impl.MlKem.AArch64.Kem16P.encryptRestP (prfW c) Impl.MlKem1024.AArch64.lay1024
        (Impl.MlKem.AArch64.Kem16P.placed Impl.MlKem1024.AArch64.lay1024 (Impl.MlKem.AArch64.Hybrid.hashPairs
          (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024))) .x25 0 .x28 KEM.MB .x27 0)
        (.block Impl.MlKem1024.AArch64.lay1024.kemEpilogue)) h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem matrixP768_depth (v : Proof.Sha3.AArch64.Permutation) :
    (Impl.MlKem.AArch64.Kem16P.matrixP sha3 lay768 (Impl.MlKem.AArch64.Hybrid.ekSrc lay768)
      (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash v.callee))).aarch64Depth ≤ 8 := by
  cases sha3
  · exact Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
        (e := Impl.MlKem.AArch64.Kem16P.matrixP false lay768 (Impl.MlKem.AArch64.Hybrid.ekSrc lay768)
          (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash hole)))
        (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)
  · exact Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
        (e := Impl.MlKem.AArch64.Kem16P.matrixP true lay768 (Impl.MlKem.AArch64.Hybrid.ekSrc lay768)
          (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash hole)))
        (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)

theorem matrixP1024_depth (v : Proof.Sha3.AArch64.Permutation) :
    (Impl.MlKem.AArch64.Kem16P.matrixP sha3 Impl.MlKem1024.AArch64.lay1024
      (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024)
      (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash v.callee))).aarch64Depth ≤ 8 := by
  cases sha3
  · exact Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
        (e := Impl.MlKem.AArch64.Kem16P.matrixP false Impl.MlKem1024.AArch64.lay1024
          (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024)
          (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash hole)))
        (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)
  · exact Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
        (e := Impl.MlKem.AArch64.Kem16P.matrixP true Impl.MlKem1024.AArch64.lay1024
          (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024)
          (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash hole)))
        (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)

/-! ## ML-KEM-768 -/

theorem encapsP768_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContractS (encapsAArch64S lay768)).pre (entryContractS (encapsAArch64S lay768)).pub
      (Impl.MlKem.AArch64.Kem16P.encaps sha3 (fixedHash v.callee) (prfW v.callee) lay768) :=
  encapsP_ct (sha3 := sha3) (fixedHash v.callee) (prfW v.callee) VG.Proof.MlKem.AArch64.KeyGen.wf768 (enG768_correct v)
    srcOk768 hashOk768 habs768 startH768_taint (g_taint v.callee (symSums v))
    (restP768_taint v.callee (symSums v))

/-- The correctness of `Kem16P.encaps` for ML-KEM-768, of its internal contract. -/
theorem encapsP768_correct (v : Proof.Sha3.AArch64.Permutation) :
    ∀ s, (entryContractS (encapsAArch64S lay768)).pre s →
      ∃ t s', Exec isa (Impl.MlKem.AArch64.Kem16P.encaps sha3 (fixedHash v.callee) (prfW v.callee) lay768) s t s' ∧
        abiPreserved s s' ∧ (entryContractS (encapsAArch64S lay768)).post s s' := by
  intro s h
  have ss := preS h.1
  have ts := entryS_tables h
  exact using_correctP (sha3 := sha3) (fixedHash v.callee) (prfW_valid v) (enG768_correct v)
    (kem_unstrip (Encaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 ss.1)) ⟨ss.2.sp, ss.2.args⟩ srcOk768
    hashOk768 Noise.room768 VG.Proof.MlKem.AArch64.Encaps.calls768 ts.1 ts.2 (by decide) (by decide)
    (matrixP768_depth (sha3 := sha3) v)

theorem encapsP768_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (Impl.MlKem.AArch64.Kem16P.encaps sha3 (fixedHash v.callee) (prfW v.callee) lay768)
      encapsH768Contract := by
  refine Verified.of_correct (T := AArch64.target) (k := entryContractS (encapsAArch64S lay768)) (encapsP768_correct (sha3 := sha3) v)
    (encapsP768_ct (sha3 := sha3) v) ?_
  · exact ⟨fun _ h => encapsH768_entry h, fun _ _ h hp => encapsH768_post h hp,
      fun _ _ hs ht hp => encapsH768_pub hs ht hp, encapsH768_sat⟩

/-! ## ML-KEM-1024 -/

theorem encapsP1024_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pre
      (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pub
      (Impl.MlKem.AArch64.Kem16P.encaps sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024) :=
  encapsP_ct (sha3 := sha3) (fixedHash v.callee) (prfW v.callee) VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 (enG1024_correct v)
    srcOk1024 hashOk1024 habs1024 startH1024_taint (g_taint v.callee (symSums v))
    (restP1024_taint v.callee (symSums v))

/-- The correctness of `Kem16P.encaps` for ML-KEM-1024, of its internal contract. -/
theorem encapsP1024_correct (v : Proof.Sha3.AArch64.Permutation) :
    ∀ s, (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pre s →
      ∃ t s', Exec isa (Impl.MlKem.AArch64.Kem16P.encaps sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024) s t s' ∧
        abiPreserved s s' ∧ (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).post s s' := by
  intro s h
  have ss := preS h.1
  have ts := entryS_tables h
  exact using_correctP (sha3 := sha3) (fixedHash v.callee) (prfW_valid v) (enG1024_correct v)
    (kem_unstrip (Encaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 ss.1)) ⟨ss.2.sp, ss.2.args⟩
    srcOk1024 hashOk1024 Noise.room1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024 ts.1 ts.2 (by decide)
    (by decide) (matrixP1024_depth (sha3 := sha3) v)

theorem encapsP1024_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target
      (Impl.MlKem.AArch64.Kem16P.encaps sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
      encapsH1024Contract := by
  refine Verified.of_correct (T := AArch64.target)
    (k := entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)) (encapsP1024_correct (sha3 := sha3) v) (encapsP1024_ct (sha3 := sha3) v) ?_
  · exact ⟨fun _ h => encapsH1024_entry h, fun _ _ h hp => encapsH1024_post h hp,
      fun _ _ hs ht hp => encapsH1024_pub hs ht hp, encapsH1024_sat⟩

end VG.Proof.MlKem.AArch64.Kem16P
