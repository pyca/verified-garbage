module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgB
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Pair
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixFrame
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastSpecPost
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SpecPost

/-! ### `MlKem.AArch64.Optimized.KeyGenMatrixPair`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Optimized.KeyGenMatrixPost`, which this module and modules that import it used -/

section

/-! # Advance the existing key-generation matrix invariant by a pair -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}

theorem BInvW.singleton {w16 : Bool} {s₀ s t : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : BInvW w16 P s₀ e s)
    (ht : Paired.LastOutcomeW w16 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))
      (kA s₀ 3+BitVec.ofNat 64 SS) (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) s t) :
    BInvW w16 P s₀ (e+1) t := by
  have hw := hp.wf
  have fr : Frame (lastWrites s₀ e) s.mem t.mem := ht.frame
  have old {i : Nat} (hi : i<e) := last_far hp he (b:=3) (o:=AH+1024*i) (l:=1024)
    (by decide) (by simp only [kL]; lom) (.inr (by lom))
  refine ⟨last_kb hp he h.kb ht.keep fr,?_,?_,?_,?_,?_⟩
  · rw [bytesAt_frame fr (last_far hp he (by decide) (by kl) (.inr (by lom))) (by decide)]
    exact h.rho
  · rw [bytesAt_frame fr (last_far hp he (by decide) (by kl) (.inr (by lom))) (by decide)]
    exact h.sig
  · rw [ht.status,h.acc]
    by_cases ha : allOk P s₀ e <;>
      by_cases hb : (sampleNTT 280 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))).isSome <;>
      simp [allOk_succ,ha,hb]
  · intro i hi
    rcases (by omega_using [hi] : i<e ∨ i=e) with hi|rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reduced
  · intro i hi
    rcases (by omega_using [hi] : i<e ∨ i=e) with hi|rfl
    · rw [aAtW,polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.result

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! ### `MlKem.AArch64.Optimized.KeyGenMatrixTable`, which this module and modules that import it used -/

section

/-! # Preserve the immutable rejection table across key-generation matrix entries -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
variable {P : KemLay}

structure MatrixTable (P : KemLay) (s₀ s : State) : Prop where
 artifact : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE")
 readable : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr)
 apart : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨kA s₀ 3,P.scl⟩

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! # Invoke the paired sampler in the existing key-generation workspace -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
variable {P : KemLay}

theorem matrixEntry_fit (hw : P.Wf) {e : Nat} (he : e<P.k*P.k) :
    AH+1024*e+1024≤kL P 3 := by
  have hf := hw.facts
  simp only [AH,kL]
  omega_using [he, hf]

theorem pair_context {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.Context (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have tab := tb.artifact
  have tr := tb.readable
  have td := tb.apart
  have hw := hp.wf
  have f0 : SS+2048≤kL P 3 := by kl
  have f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw (by omega_using [he])
  have f2 : AH+1024*(e+1)+1024≤kL P 3 := matrixEntry_fit hw he
  have apart {o l : Nat} (fit : o+l≤P.scl) :
      (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint (R (kA s₀) 3 o l) :=
    td.sub_right (Offset.sub_base (kA s₀ 3) fit)
  have ctx : Paired.Context (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
    refine ⟨cov_w hp h (b:=3) (o:=SS) (l:=2048) (by decide) f0,cov_w hp h (b:=3) (o:=AH+1024*e) (l:=1024) (by decide) f1,
      cov_w hp h (b:=3) (o:=AH+1024*(e+1)) (l:=1024) (by decide) f2,?_,?_,?_,tab,tr,apart f0,apart f1,apart f2⟩
    · exact hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SS) (l₁:=2048) (o₂:=AH+1024*e) (l₂:=1024) (by decide) (by decide) f0 f1 (by lom)
    · exact hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SS) (l₁:=2048) (o₂:=AH+1024*(e+1)) (l₂:=1024) (by decide) (by decide) f0 f2 (by lom)
    · exact hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=AH+1024*e) (l₁:=1024) (o₂:=AH+1024*(e+1)) (l₂:=1024) (by decide) (by decide) f1 f2 (by omega_using [])
  exact ctx

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! # The odd final matrix entry in key generation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
variable {P : KemLay}

theorem singleton_context {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.SingleContext (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  have f0 : SS+2048≤kL P 3 := by kl
  have f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw he
  have ctx : Paired.SingleContext (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
    refine ⟨cov_w hp h (b:=3) (o:=SS) (l:=2048) (by decide) f0,
      cov_w hp h (b:=3) (o:=AH+1024*e) (l:=1024) (by decide) f1,
      hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SS) (l₁:=2048) (o₂:=AH+1024*e) (l₂:=1024)
        (by decide) (by decide) f0 f1 (by lom),tb.artifact,tb.readable,?_,?_⟩
    · exact tb.apart.sub_right (Offset.sub_base (kA s₀ 3) f0)
    · exact tb.apart.sub_right (Offset.sub_base (kA s₀ 3) f1)
  exact ctx

end VG.Proof.MlKem.AArch64.KeyGen
