module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.AArch64.KgB
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.DotReady
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Loop
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Result
import VerifiedGarbage.Proof.MlKem.AArch64.AddSubW
import VerifiedGarbage.Proof.MlKem.AArch64.DotW
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
public import VerifiedGarbage.Impl.MlKem.AArch64.Ops16
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrefix
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Pair
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastSpecPost
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SpecPost
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullSample
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Restore
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon

/-! ### `MlKem.AArch64.Optimized.KeyGenMatrixLast`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Optimized.KeyGenMatrixFrame`, which only this module used -/

section

/-! # Memory and caller invariants for two matrix entries at a time -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
variable {P : KemLay}

def pairWrites (s₀ : State) (e : Nat) : List Region :=
  Paired.stepWrites (kA s₀ 3+BitVec.ofNat 64 SS)
    (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
    (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1)))

theorem pair_far {s₀ : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    {b o l : Nat} (hb : b<4) (hf : o+l≤kL P b)
    (hs : b≠3 ∨ ((o+l≤SS ∨ SS+2048≤o) ∧
      (o+l≤AH+1024*e ∨ AH+1024*(e+2)≤o))) :
    ∀r∈pairWrites s₀ e,(R (kA s₀) b o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact hp.args.rdisj hb (by decide) hf (by kl) (by rcases hs with hs|hs <;> omega_using [hs])
  · exact hp.args.rdisj hb (by decide) hf (by simp only [kL]; lom)
      (by rcases hs with hs|hs <;> omega_using [hs])
  · exact hp.args.rdisj hb (by decide) hf (by simp only [kL]; lom)
      (by rcases hs with hs|hs <;> omega_using [hs])

def lastWrites (s₀ : State) (e : Nat) : List Region :=
  Paired.fullWrites (kA s₀ 3+BitVec.ofNat 64 SS)
    (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))

theorem last_far {s₀ : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    {b o l : Nat} (hb : b<4) (hf : o+l≤kL P b)
    (hs : b≠3 ∨ ((o+l≤SS ∨ SS+2048≤o) ∧
      (o+l≤AH+1024*e ∨ AH+1024*(e+1)≤o))) :
    ∀r∈lastWrites s₀ e,(R (kA s₀) b o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hp.args.rdisj hb (by decide) hf (by kl) (by rcases hs with hs|hs <;> omega_using [hs])
  · exact hp.args.rdisj hb (by decide) hf (by simp only [kL]; lom)
      (by rcases hs with hs|hs <;> omega_using [hs])

theorem last_kb {s₀ s t : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P s₀ s) (hk : Keep Paired.pairRegs s t) (hf : Frame (lastWrites s₀ e) s.mem t.mem) :
    KB P s₀ t := by
  have hw := hp.wf
  have h1 := last_far hp he (b:=3) (o:=SV P) (l:=48) (by decide) hp.sv (.inr (by lom))
  have h2 := last_far hp he (b:=0) (o:=0) (l:=64) (by decide) (by kl) (.inl (by decide))
  exact h.frame hk hf (by decide) fun r hr=>⟨h1 r hr,h2 r hr⟩

end VG.Proof.MlKem.AArch64.KeyGen

end

end

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

end

end

/-! ### `MlKem.AArch64.Optimized.KeyGenMatrixTiming`, which this module and modules that import it used -/

section

/-! # Public-seed timing of the optimized encryption matrix -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
open VG.Proof.MlKem
variable {P : KemLay}

theorem pair_input {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.BeginInput SB SS (AH+1024*e) (AH+1024*(e+1))
      ((kA s₀ 3+BitVec.ofNat 64 SS)) ((kA s₀ 3+BitVec.ofNat 64 SB)) ((kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))) ((kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨(by rw [h.x28]),(by rw [h.x28]),(by rw [h.x28]),(by rw [h.x28]),?_,
    hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=SS) (l₂:=2048) (by decide) (by decide) (by kl) (by kl) (by decide),pair_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_r hp h (b:=3) (o:=SB) (l:=32) (by decide) (by kl)) (k:=8*j) (by omega_using [hj]) (by omega_using [])

theorem last_input {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.LastInput SB SS (AH+1024*e) ((kA s₀ 3+BitVec.ofNat 64 SS)) ((kA s₀ 3+BitVec.ofNat 64 SB)) ((kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨(by rw [h.x28]),(by rw [h.x28]),(by rw [h.x28]),?_,
    hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=SS) (l₂:=2048) (by decide) (by decide) (by kl) (by kl) (by decide),singleton_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_r hp h (b:=3) (o:=SB) (l:=32) (by decide) (by kl)) (k:=8*j) (by omega_using [hj]) (by omega_using [])

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! ### `MlKem.AArch64.KgH.Row`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.KgH.Inv`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Kem16.KgRows`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Kem16.KgCommon`, which this module and modules that import it used -/

section

/-! # The 16-bit key generation's invariants

With `Â` and `ŝ` stored with 16 bits, over the first `n` entries of `Â`: what
the computation of `ŝ`, `ê` and `t̂` keeps (`CInvW`: `ρ`, `σ`, `x24`, and `Â` as
the matrix left it), what holds after `t̂[i']` for `i' < i` (`TLW`) and from
the copies of `ρ` on (`EndInvW`), and what the function leaves (`DoneW`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Proof.MlKem (cw)

variable {P : KemLay}

structure CInvW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (n : Nat) (s : State) : Prop where
  kb : KB P s₀ s
  rho : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SB) 32 = rhoK P s₀
  sig : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 32 = KPke.kgSigma P.params (dB s₀)
  x24 : s.gpr .x24 = v
  le : n ≤ P.k * P.k
  ahat : ∀ e < n, ReducedW 16 s.mem (AR s₀ e) ∧ polyAtW 16 s.mem (AR s₀ e) = polyAtW 16 mB (AR s₀ e)

theorem CInvW.frame {s₀ : State} {mB : Mem} {v : BitVec 64} {n : Nat} {s s' : State} (h : CInvW P s₀ mB v n s)
    (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r) : CInvW P s₀ mB v n s' := by
  have hle := h.le
  have ha : ∀ e < n, ∀ r ∈ W, (polyRegion (AR s₀ e)).Disjoint r := fun e he r hr =>
    (hW r hr).2.2.sub_left (by
      rw [show AR s₀ e = kA s₀ 3 + BitVec.ofNat 64 AH + BitVec.ofNat 64 (1024 * e) by rw [ptr_add]]
      exact sub_offset' (by omega_using [hle, he]))
  refine ⟨hk, ?_, ?_, by rw [hx, h.x24], hle, fun e he => ⟨reducedW_frame (w16 := true) hf (ha e he) (h.ahat e he).1, ?_⟩⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.rho
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.sig
  · exact (polyAtW_frame (w16 := true) hf (ha e he)).trans (h.ahat e he).2

abbrev aMW (P : KemLay) (s₀ : State) (mB : Mem) (i j : Nat) : Poly := polyAtW 16 mB (AR s₀ (P.k * i + j))

abbrev tVW (P : KemLay) (s₀ : State) (mB : Mem) (i : Nat) : Poly := KPke.kgT P.params (aMW P s₀ mB) (dB s₀) i

structure TLW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (n i : Nat) (s : State) : Prop where
  c : CInvW P s₀ mB v n s
  sp : ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  dk : ∀ j < P.k, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j)) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j)
  ek : ∀ i' < i, bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * i')) 384 = encode12 (tVW P s₀ mB i') ∧
    bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * P.k + 384 * i')) 384 = encode12 (tVW P s₀ mB i')

theorem TLW.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n i : Nat} {s s' : State}
    (h : TLW P s₀ mB v n i s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Apart P s₀ i r) : TLW P s₀ mB v n i s' := by
  have hw := hp.wf
  refine ⟨h.c.frame hk hx hf fun r hr => ⟨(hW r hr).1, (hW r hr).2.1,
    (hW r hr).2.2.1.sub_left (R.sub2 (Nat.le_refl _) (by omega_using []))⟩, fun j hj => ?_, fun j hj => ?_,
    fun i' hi' => ⟨?_, ?_⟩⟩
  · exact polyIsW_frame_poly (w16 := true) hf (fun r hr => (hW r hr).2.2.1.sub_left (R.sub2 (by lom) (by lom))) (h.sp j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega_using [])
      (by have := mul_succ_le (a := 384) hj; omega_using [hj]))) (by decide)]
    exact h.dk j hj
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left (R.sub2 (by omega_using [])
      (by have := mul_succ_le (a := 384) hi'; omega_using [hi']))) (by decide)]
    exact (h.ek i' hi').1
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega_using [])
      (by have := mul_succ_le (a := 384) hi'; omega_using [hi']))) (by decide)]
    exact (h.ek i' hi').2

structure DoneW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  ek : bytesAt s.mem (kA s₀ 1) P.ekLen = KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)
  dk : bytesAt s.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
    KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀) ++ H (KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)) ++ zB s₀

structure EndInvW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (n : Nat) (s : State) : Prop where
  tl : TLW P s₀ mB v n P.k s
  rek : bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * P.k)) 32 = rhoK P s₀
  rdk : bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k)) 32 = rhoK P s₀

theorem EndInvW.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n : Nat} {s s' : State}
    (h : EndInvW P s₀ mB v n s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Far P s₀ r) : EndInvW P s₀ mB v n s' :=
  ⟨h.tl.frame hp hk hx hf fun r hr => (hW r hr).1,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.rek,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2) (by decide)]; exact h.rdk⟩

theorem rho_okW {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n : Nat} {s : State}
    (h : TLW P s₀ mB v n P.k s) :
    WP isa (.block (copy32 .x28 SB .x26 (384 * P.k) ++ copy32 .x28 SB .x27 (768 * P.k))) s fun s' =>
      KB P s₀ s' ∧ EndInvW P s₀ mB v n s' ∧
        Frame [R (kA s₀) 1 (384 * P.k) 32, R (kA s₀) 2 (768 * P.k) 32] s.mem s'.mem := by
  have hw := hp.wf
  have kb := h.c.kb
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 1) (so := SB) (dO := 384 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb.x28 kb.x26 (cov_r hp kb (b := 3) (by decide) (by kl))
    (cov_w hp kb (b := 1) (by decide) (by kl))) fun sa ⟨ka, fa, ba⟩ => ?_
  have kba := kb.frame ka fa (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 1) (o := 384 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have tla := h.frame hp kba (ka.get .x24) fa fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 1) (o := 384 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (fun _ => Nat.le_refl _) (by kl)
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 2) (so := SB) (dO := 768 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kba.x28 kba.x27 (cov_r hp kba (b := 3) (by decide) (by kl))
    (cov_w hp kba (b := 2) (by decide) (by kl))) fun sb ⟨kb', fb, bb⟩ => ?_
  have kbb := kba.frame kb' fb (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  refine ⟨kbb, ⟨tla.frame hp kbb (kb'.get .x24) fb (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 2) (o := 768 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (by kl) (fun _ => by omega_using [])), ?_, ?_⟩, ?_⟩
  · rw [bytesAt_frame fb (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide), ba]
    exact h.c.rho
  · rw [bb, bytesAt_frame fa (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact h.c.rho
  · exact (fa.mono (by simp)).trans (fb.mono (by simp))

theorem post_ofW {s₀ sB s' : State} (hB : BInvW true P s₀ (P.k * P.k) sB) (hD : DoneW P s₀ sB.mem (sB.gpr .x24) s') :
    (keyGenAArch64 P).post s₀ s' := by
  show Outcome (fun iters => keyGenInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) 32)
    (bytesAt s₀.mem (s₀.gpr .x0 + 32) 32)) ((s'.gpr .x0).setWidth 32)
    (bytesAt s'.mem (s₀.gpr .x1) P.ekLen, bytesAt s'.mem (s₀.gpr .x2) P.dkLen)
  have ed : bytesAt s₀.mem (s₀.gpr .x0) 32 = dB s₀ := by
    show _ = bytesAt s₀.mem (s₀.gpr .x0 + BitVec.ofNat 64 0) 32
    rw [ptr_zero]
  have ez : bytesAt s₀.mem (s₀.gpr .x0 + 32) 32 = zB s₀ := rfl
  have ek : bytesAt s'.mem (s₀.gpr .x1) P.ekLen = KPke.ekPKE P.params (aMW P s₀ sB.mem) (dB s₀) := hD.ek
  have dk : bytesAt s'.mem (s₀.gpr .x2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      KPke.ekPKE P.params (aMW P s₀ sB.mem) (dB s₀) ++ H (KPke.ekPKE P.params (aMW P s₀ sB.mem) (dB s₀)) ++
      zB s₀ := hD.dk
  rw [ed, ez, ek, dk, hD.x0, hB.acc]
  by_cases hA : allOk P s₀ (P.k * P.k)
  · rw [ite_eq_left hA]
    refine .inl ⟨rfl, 280, ?_⟩
    show keyGenInternal P.params 280 (dB s₀) (zB s₀) = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some (p := P.params) rfl (a := aMW P s₀ sB.mem)
      fun i hi j hj => ?_]
    · rfl
    · have hi : i < P.k := hi
      have hj : j < P.k := hj
      have he : P.k * i + j < P.k * P.k := ij_lt hi hj
      have hke := ij_div (i := i) hj
      have r := hB.res (P.k * i + j) he
      have ok := hA (P.k * i + j) he
      rw [hke.1, hke.2] at r ok
      rcases r with r | r
      · rw [r] at ok; simp at ok
      · exact r
  · rw [ite_eq_right hA]
    refine .inr ⟨rfl, ?_⟩
    obtain ⟨e, he, hn⟩ : ∃ e, e < P.k * P.k ∧ ¬ (sampleNTT 280 (matSeed (rhoK P s₀) (e / P.k) (e % P.k))).isSome :=
      Classical.byContradiction fun hc => hA fun e he => Classical.byContradiction fun hn => hc ⟨e, he, hn⟩
    show keyGenInternal P.params 280 _ _ = none
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none (p := P.params) (i := e / P.k) (j := e % P.k)
      (div_lt he) (mod_lt he) (Option.not_isSome_iff_eq_none.mp hn)]
    rfl

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! ### `MlKem.AArch64.Kem16.KgOps`, which only this module used -/

section

/-! # The building blocks of the 16-bit key generation

As `Kem16/Ops.lean`, in key generation's context (`KeyGen.KB`): the fused dot
product (`fusedW_tl`), the sum (`addW_read_okK`) and `ByteEncode₁₂`
(`enc12W_okK`) of polynomials stored with 16 bits. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64.DotW (half_sub)
variable {P : KemLay}

theorem fusedW_tl {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n i : Nat}
    (hi : i < P.k) (h : TLW P s₀ mB v n i s) (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28 + BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA") terms
      (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues) :
    WP isa (Kem16.dotAt (TP P) terms) s fun s' =>
      TLW P s₀ mB v n i s' ∧
      Frame [R (kA s₀) 3 (TP P) 1024] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) (Dot.polySum terms F G) := by
  have hw := hp.wf
  refine WP.mono (DotW.dotW_ok (by decide) (by lom) terms hd) fun t ⟨hk,hf,hpoly⟩ => ?_
  rw [h.c.kb.x28] at hf hpoly
  have hf' : Frame [R (kA s₀) 3 (TP P) 1024] s.mem t.mem :=
    hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  have hkb : KB P s₀ t := h.c.kb.frame hk hf' (by decide) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (by decide) (by kl) (by kl) (by decide))
  exact ⟨h.frame hp hkb (hk.get .x24 (by decide)) hf' (apart_TP hp hi),hf',hpoly⟩

theorem addW_read_okK {s₀ : State} (hp : Pre P s₀) {f g : Nat} (hf : PolyOff P f) (hg : g + 1024 ≤ P.scl)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P s₀ s)
    (rf : ReducedW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 f)) (rg : ReducedW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 g)) :
    WP isa (Kem16.addWAt f g) s fun s' => KB P s₀ s' ∧ Frame [R (kA s₀) 3 f 1024] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (kA s₀ 3 + BitVec.ofNat 64 f)
        (add (polyAtW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 f)) (polyAtW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨hf1, hf2⟩ := hf
  have ff : f + 1024 ≤ kL P 3 := by kl
  have fg : g + 1024 ≤ kL P 3 := by kl
  refine WP.seq (wp_ptrTo (by decide) (by kl) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kl)
    fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x0 : s₂.gpr .x0 = kA s₀ 3 + BitVec.ofNat 64 f := by rw [h₂.get .x0, e₁, hk.x28]
  have x1 : s₂.gpr .x1 = kA s₀ 3 + BitVec.ofNat 64 g := by rw [e₂, h₁.get .x28, hk.x28]
  have cw := cov_w hp kb₂ (b := 3) (by decide) ff
  have cr := cov_r hp kb₂ (b := 3) (by decide) fg
  refine WP.mono (AddSubW.addW_ok ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_⟩) fun s₃ ⟨k₃,f₃,p₃⟩ => ?_
  · rw [x0]; exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x1]; exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x0, x1]
    exact ((hp.args.rdisj (by decide) (by decide) ff fg (by omega_using [d])).sub_left (half_sub _)).sub_right
      (half_sub _)
  · rw [x0, m₂]; exact rf
  · rw [x1, m₂]; exact rg
  rw [x0, x1, m₂] at p₃
  rw [x0] at f₃
  have f₃' : Frame [R (kA s₀) 3 f 1024] s₂.mem s₃.mem :=
    f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  refine ⟨kb₂.frame k₃ f₃' (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact kb_disj hp (by decide) ff (by kl) (by decide),
    by rw [← m₂]; exact f₃', p₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem enc12W_okK {s₀ : State} (hp : Pre P s₀) {off b o : Nat} (ho : PolyOff P off) (hb : b = 1 ∨ b = 2)
    (fo : o + 384 ≤ kL P b) {s : State} (hk : KB P s₀ s) {F : Poly}
    (hr : PolyIsW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 off) F) :
    WP isa (Kem16.enc12WAt off (breg b) o) s fun s' => KB P s₀ s' ∧ Frame [R (kA s₀) b o 384] s.mem s'.mem ∧
      bytesAt s'.mem (kA s₀ b + BitVec.ofNat 64 o) 384 = encode12 F ∧ s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨ho1, ho2⟩ := ho
  have hb4 : b < 4 := by omega_using [hb]
  have fo3 : off + 1024 ≤ kL P 3 := by kl
  have hol : o < 65536 := by have := kL_le hp.wf b; omega_using [fo, this]
  have hx : Reg.x1 ≠ breg b := by rcases hb with rfl | rfl <;> decide
  have hx0 : breg b ≠ Reg.x0 := by rcases hb with rfl | rfl <;> decide
  refine WP.seq (wp_ptrTo (by decide) (by kl) fun s₁ h₁ e₁ => wp_ptrTo' hx hol fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x0 : s₂.gpr .x0 = kA s₀ 3 + BitVec.ofNat 64 off := by rw [h₂.get .x0, e₁, hk.x28]
  have x1 : s₂.gpr .x1 = kA s₀ b + BitVec.ofNat 64 o := by
    rw [e₂, h₁.get (breg b) (by simpa using hx0), hk.breg hb4]
  have cr := cov_r hp kb₂ (b := 3) (by decide) fo3
  have cw := cov_w hp kb₂ ⟨by omega_using [hb], hb4⟩ fo
  refine WP.mono (Codec12W.encW_ok (P := F) x0 x1 ⟨by rw [m₂]; exact hr, fun j hj => ?_, fun j n hj => ?_, ?_⟩)
    fun s₃ ⟨k₃,f₃,b₃⟩ => ?_
  · exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · exact (hp.args.rdisj (b₁ := 3) (o₁ := off) (l₁ := 1024) (by decide) hb4 fo3 fo (by omega_using [hb])).sub_left
      (half_sub _)
  refine ⟨kb₂.frame k₃ f₃ (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact kb_disj hp hb4 fo (.inl (by omega_using [hb])) (by omega_using [hb]),
    by rw [← m₂]; exact f₃, b₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! # The 16-bit key generation's steps

As `Optimized/KeyGen*.lean`, with 16 bits: the noise, the encodings of `ŝ`
(`encode_okW`), and a row of `t̂` (`row_readyW`, `fused_row_readyW`: the
fused dot product, the sum with `ê` and the encodings), which
`KgH/` composes into `Kem16P.keyGen`. -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Optimized/KeyGenMatrix.lean`, which only this module imported.

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Optimized/KeyGenFinish.lean`, which only this module imported.

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
open VG.Proof.MlKem.AArch64.Optimized
variable {P : KemLay}

def rowFW (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 fg.1)
def rowGW (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 fg.2)

/-- Entry `j` of row `i` is among the first `n`, once the first `i + 1` rows are. -/
theorem lt_row {i j n : Nat} (hn : P.k * (i + 1) ≤ n) (hj : j < P.k) : P.k * i + j < n := by
  rw [Nat.mul_succ] at hn; omega_using [hn, hj]

theorem row_sumW {s₀ s : State} {mB : Mem} {v : BitVec 64} {n i : Nat}
    (hn : P.k * (i + 1) ≤ n) (h : TLW P s₀ mB v n i s) :
    Dot.polySum (rowTerms P i) (rowFW s₀ s) (rowGW s₀ s) =
      KPke.dotK (aMW P s₀ mB i) (KPke.kgS P.params (dB s₀)) P.k := by
  apply Optimized.polySum_dotK
  · intro j hj
    exact (h.c.ahat (P.k*i+j) (lt_row hn hj)).2
  · intro j hj
    exact (h.sp j hj).2

theorem row_readyW {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n i : Nat}
    (hi : i < P.k) (hn : P.k * (i + 1) ≤ n) (h : TLW P s₀ mB v n i s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (s.gpr .x28+BitVec.ofNat 64 (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    DotW.ReadyW s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (rowTerms P i) (rowFW s₀ s) (rowGW s₀ s) := by
  have hw := hp.wf
  have term : ∀ fg ∈ rowTerms P i, ∃ j<P.k, fg=(aOff P i j,sOff P j) := by
    intro fg hf
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
    exact ⟨j,List.mem_range.mp hj,rfl⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,ha,hc,ht⟩
  · simp only [rowTerms,List.length_map,List.length_range]; exact hw.facts.2.1
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf; have hij := ij_lt hi hj; change aOff P i j < 65536; lom
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf; have hij := ij_lt hi hj; change sOff P j < 65536; lom
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact ⟨(h.c.ahat (P.k*i+j) (lt_row hn hj)).1,rfl⟩
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact ⟨(h.sp j hj).1,rfl⟩
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by lom)
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by lom)
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact cov_r hp h.c.kb (b := 3) (by decide) (by kl)
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact cov_r hp h.c.kb (b := 3) (by decide) (by kl)
  · rw [h.c.kb.x28]
    exact cov_w hp h.c.kb (b := 3) (by decide) (by kl)

theorem fused_rowW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} {n i : Nat} (hi : i < P.k) (h : TLW P s₀ mB v n i s)
    {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (rowTerms P i) (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues)
    (hsum : Dot.polySum (rowTerms P i) F G = KPke.dotK (aMW P s₀ mB i) (KPke.kgS P.params (dB s₀)) P.k)
    (he : PolyIsW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 (noiseOff P i)) (KPke.kgE P.params (dB s₀) i)) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgRow P i) s fun t =>
      TLW P s₀ mB v n (i+1) t ∧ Frame (rowWrites P s₀ i) s.mem t.mem := by
  have hw := hp.wf
  have eg := Noise.noise_fits hr hi
  have ep := Noise.noise_past_kg hr i
  change WP isa (seqs [_,_,_,_]) s _
  refine WP.seq (WP.mono (fusedW_tl hp hi h (rowTerms P i) hd) fun s₂ ⟨tl₂,f₂,t₂⟩ => ?_)
  rw [hsum] at t₂
  have e₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ (fun r hr' => by
    rw [List.mem_singleton.mp hr']
    exact hp.args.rdisj (by decide) (by decide) eg (by kl) (by lom)) he
  refine WP.seq (WP.mono (addW_read_okK hp (f := TP P) (g := noiseOff P i) (po_TP hw) eg
    (.inl (by lom)) tl₂.c.kb t₂.1 e₂.1) fun s₇ ⟨kb₇,f₇,t₇,x₇⟩ => ?_)
  have tl₇ := tl₂.frame hp kb₇ x₇ f₇ (apart_TP hp hi)
  rw [t₂.2,e₂.2] at t₇
  have tv : PolyIsW 16 s₇.mem (kA s₀ 3+BitVec.ofNat 64 (TP P)) (tVW P s₀ mB i) := t₇
  refine WP.seq (WP.mono (enc12W_okK hp (off := TP P) (b := 1) (o := 384*i) (po_TP hw) (.inl rfl)
    (by kl) kb₇ tv) fun s₈ ⟨kb₈,f₈,b₈,x₈⟩ => ?_)
  have tl₈ := tl₇.frame hp kb₈ x₈ f₈ fun r hr' => by
    rw [List.mem_singleton.mp hr']; exact apart_ek hp hi
  have tv₈ : PolyIsW 16 s₈.mem _ _ := polyIsW_frame_poly (w16 := true) f₈ (fun r hr' => by
    rw [List.mem_singleton.mp hr']
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) tv
  refine WP.mono (enc12W_okK hp (off := TP P) (b := 2) (o := 384*P.k+384*i) (po_TP hw) (.inr rfl)
    (by kl) kb₈ tv₈) fun s₉ ⟨kb₉,f₉,b₉,x₉⟩ => ?_
  have tl₉ := tl₈.frame hp kb₉ x₉ f₉ fun r hr' => by
    rw [List.mem_singleton.mp hr']; exact apart_dk hp hi
  refine ⟨⟨tl₉.c,tl₉.sp,tl₉.dk,fun i' hi' => ?_⟩,?_⟩
  · rcases (by omega_using [hi'] : i'<i ∨ i'=i) with hi' | rfl
    · exact tl₉.ek i' hi'
    · refine ⟨?_,b₉⟩
      rw [bytesAt_frame f₉ (fun r hr' => by
        rw [List.mem_singleton.mp hr']
        exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) (by decide),b₈]
  · exact (((f₂.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites])).trans
      (f₇.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites]))).trans
      (f₈.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites]))).trans
      (f₉.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites]))

def ErrorsK (P : KemLay) (s₀ s : State) : Prop :=
  ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 (noiseOff P j)) (KPke.kgE P.params (dB s₀) j)

theorem errors_rowW {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {i : Nat} (hi : i < P.k) (he : ErrorsK P s₀ s)
    (hf : Frame (rowWrites P s₀ i) s.mem t.mem) : ErrorsK P s₀ t := by
  have hw := hp.wf
  intro j hj
  have eg := Noise.noise_fits hr hj
  have ep := Noise.noise_past_kg hr j
  apply polyIsW_frame_poly (w16 := true) hf _ (he j hj)
  intro r hm
  simp only [rowWrites,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact hp.args.rdisj (by decide) (by decide) eg (by kl) (by lom)
  · exact hp.args.rdisj (by decide) (by decide) eg (by kl) (.inl (by decide))
  · exact hp.args.rdisj (by decide) (by decide) eg (by kl) (.inl (by decide))

theorem fused_row_readyW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} {n i : Nat} (hi : i < P.k) (hn : P.k * (i + 1) ≤ n)
    (h : TLW P s₀ mB v n i s) (he : ErrorsK P s₀ s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (s.gpr .x28+BitVec.ofNat 64 (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgRow P i) s fun t =>
      TLW P s₀ mB v n (i+1) t ∧ ErrorsK P s₀ t ∧ Frame (rowWrites P s₀ i) s.mem t.mem := by
  exact WP.mono (fused_rowW hp hr hi h (row_readyW hp hi hn h ht hc ha).data (row_sumW hn h) (he i hi))
    fun t ⟨h',hf⟩ => ⟨h',errors_rowW hp hr hi he hf,hf⟩

structure EncodeInvW (P : KemLay) (s₀ : State) (mB mN : Mem) (v : BitVec 64) (n j : Nat) (s : State) : Prop where
  c : CInvW P s₀ mB v n s
  sp : ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  errors : ErrorsK P s₀ s
  dk : ∀ j' < j, Spec.Sha3.bytesAt s.mem (kA s₀ 2+BitVec.ofNat 64 (384*j')) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j')
  frame : Frame [R (kA s₀) 2 0 (384*j)] mN s.mem

theorem encode_stepW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB mN : Mem} {v : BitVec 64} {n j : Nat} (hj : j < P.k) (h : EncodeInvW P s₀ mB mN v n j s) :
    WP isa (Kem16.enc12WAt (sOff P j) .x27 (384*j)) s (EncodeInvW P s₀ mB mN v n (j+1)) := by
  have hw := hp.wf
  have fd : 384*j+384 ≤ kL P 2 := by kl
  refine WP.mono (enc12W_okK hp (off := sOff P j) (b := 2) (o := 384*j)
    (po_s hw hj) (.inr rfl) fd h.c.kb (h.sp j hj)) fun t ⟨kt,ft,bt,xt⟩ => ?_
  refine ⟨h.c.frame kt xt ft (one_far hp (by decide) fd (.inl (by decide))),?_,?_,?_,?_⟩
  · intro i hi
    exact polyIsW_frame_poly (w16 := true) ft (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact hp.args.rdisj (by decide) (by decide) (by kl) fd (.inl (by decide))) (h.sp i hi)
  · intro i hi
    exact polyIsW_frame_poly (w16 := true) ft (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact hp.args.rdisj (by decide) (by decide) (Noise.noise_fits hr hi) fd (.inl (by decide))) (h.errors i hi)
  · intro i hi
    rcases (by omega_using [hi] : i<j ∨ i=j) with hi | rfl
    · rw [bytesAt_frame ft (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact hp.args.rdisj (by decide) (by decide) (by kl) fd (.inr (.inl (by omega_using [hi])))) (by decide)]
      exact h.dk i hi
    · exact bt
  · exact (h.frame.sub (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact ⟨_,List.mem_singleton_self _,R.sub2 (by omega_using []) (by omega_using [])⟩)).trans
      (ft.sub (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact ⟨_,List.mem_singleton_self _,R.sub2 (by omega_using []) (by omega_using [])⟩))

theorem encode_okW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB mN : Mem} {v : BitVec 64} {n : Nat} (h : EncodeInvW P s₀ mB mN v n 0 s) :
    WPs ((List.range P.k).map fun j => Kem16.enc12WAt (sOff P j) .x27 (384*j)) s (EncodeInvW P s₀ mB mN v n P.k) :=
  WPs.range (fun _ hj _ h => encode_stepW hp hr hj h) h

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! # Key generation hashing `ek` during the matrix: its invariant

`Kem16P.keyGen` samples `Â` pair by pair and computes each row of `t̂` as soon
as its entries are sampled, while the third state of the `x3` calls absorbs the
blocks of `ek` the rows before have encoded. `IL n r h`: after `n` entries of
`Â`, `r` rows of `t̂` (encoded into both keys, over `Â` as memory holds it) and
`h` blocks of `ek` absorbed into the third state, at `scratch`; `Stk128K`, the
128 bytes below the stack pointer those calls use. `row_step`: a row keeps it. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk hstate dB frame)
open VG.Impl.MlKem.AArch64.Noise (noiseOff)

variable {P : KemLay}

/-- The 128 bytes below the stack pointer, apart from the arguments. -/
structure Stk128K (P : KemLay) (s₀ : State) : Prop where
  sp : 128 ≤ s₀.sp.toNat
  args : ∀ b < 4, (frame s₀.sp).Disjoint ⟨kA s₀ b, kL P b⟩

theorem Stk128K.R {s₀ : State} (hk : Stk128K P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b) :
    (frame s₀.sp).Disjoint (R (kA s₀) b o l) :=
  (hk.args b hb).sub_right (R.sub f)

theorem foldK_congr {α : Type} {op : α → α → α} {z : α} {f g : Nat → α} :
    ∀ {k : Nat}, (∀ j < k, f j = g j) → KPke.foldK op z f k = KPke.foldK op z g k
  | 0, _ => rfl
  | 1, h => by simp only [KPke.foldK]; exact h 0 (by decide)
  | k + 2, h => by
    simp only [KPke.foldK]
    rw [foldK_congr (k := k + 1) (fun j hj => h j (by omega_using [hj])), h (k + 1) (by omega_using [])]

/-- Row `i` of `t̂` depends on row `i` of `Â` alone. -/
theorem tVW_congr {s₀ : State} {m m' : Mem} {i : Nat}
    (h : ∀ j < P.k, polyAtW 16 m (AR s₀ (P.k * i + j)) = polyAtW 16 m' (AR s₀ (P.k * i + j))) :
    tVW P s₀ m i = tVW P s₀ m' i := by
  simp only [tVW, KPke.kgT, KPke.dotK]
  rw [foldK_congr (fun j hj => by simp only [aMW]; rw [h j hj])]

/-- The hash of the first `b` blocks depends on their bytes alone. -/
theorem hstate_prefix {m m' : Mem} {p : Addr} {len b : Nat} {d : Byte} (hb : 136 * b ≤ len)
    (h : bytesAt m p (136 * b) = bytesAt m' p (136 * b)) :
    hstate (bytesAt m p len) b d = hstate (bytesAt m' p len) b d := by
  simp only [hstate, VG.Proof.MlKem.bytesAt_length, hb, ↓reduceIte,
    VG.Proof.MlKem.bytesAt_take _ _ hb, h]

/-- Rows `i' < r` of `t̂` encoded into both keys, over `Â` as `m` holds it. -/
def RowsDone (P : KemLay) (s₀ : State) (m : Mem) (r : Nat) : Prop :=
  ∀ i' < r, bytesAt m (kA s₀ 1 + BitVec.ofNat 64 (384 * i')) 384 = encode12 (tVW P s₀ m i') ∧
    bytesAt m (kA s₀ 2 + BitVec.ofNat 64 (384 * P.k + 384 * i')) 384 = encode12 (tVW P s₀ m i')

/-- After `G`, the noise, `ŝ` into `dk` and the all-zero third state: `n`
entries of `Â`, `r` rows of `t̂`, and `h` blocks of `ek` absorbed into the third
state (at `scratch`). -/
structure IL (P : KemLay) (s₀ : State) (n r h : Nat) (s : State) : Prop where
  b : BInvW true P s₀ n s
  sp : ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  errors : ErrorsK P s₀ s
  dk : ∀ j < P.k, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j)) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j)
  rows : RowsDone P s₀ s.mem r
  rn : P.k * r ≤ n
  le : n ≤ P.k * P.k
  rk : r ≤ P.k
  hash : stateAt s.mem (kA s₀ 3) =
    hstate (bytesAt s.mem (kA s₀ 1) P.ekLen) h (Hybrid.dB (Impl.MlKem.AArch64.Kem16.kgSrc P))
  hr : 136 * h ≤ 384 * r
  tables : Tables s
  tstk : TStk s

/-- Writes that leave the rows' memory in `scratch`'s first 200 bytes, `ek` before
`384 r` and the matrix's first `n` entries as they were. -/
theorem IL.rowsDone_frame {s₀ : State} {m m' : Mem} {n r : Nat} (hrn : P.k * r ≤ n) (hr : RowsDone P s₀ m r)
    {W : List Region} (hf : Frame W m m')
    (hA : ∀ e < n, ∀ q ∈ W, (polyRegion (AR s₀ e)).Disjoint q)
    (hE : ∀ i' < r, ∀ q ∈ W, (R (kA s₀) 1 (384 * i') 384).Disjoint q ∧
      (R (kA s₀) 2 (384 * P.k + 384 * i') 384).Disjoint q) :
    RowsDone P s₀ m' r := by
  intro i' hi'
  have ht : tVW P s₀ m' i' = tVW P s₀ m i' := tVW_congr fun j hj =>
    polyAtW_frame (w16 := true) hf (hA _ (by
      have := Nat.mul_le_mul_left P.k (show i' + 1 ≤ r by omega_using [hi'])
      rw [Nat.mul_succ] at this; omega_using [hrn, hj, this]))
  rw [ht, bytesAt_frame hf (fun q hq => (hE i' hi' q hq).1) (by decide),
    bytesAt_frame hf (fun q hq => (hE i' hi' q hq).2) (by decide)]
  exact hr i' hi'

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! # A row of `t̂` between the pairs of the matrix

`row_step`: row `r` of `t̂`, once the matrix holds its entries (`Kem16.kgRow`,
proven by `fused_row_readyW` over `Â` as memory holds it), keeps the
interleaved invariant `IL`: it writes neither the matrix, the third state, nor the
blocks of `ek` the third state has absorbed. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)

variable {P : KemLay}

theorem stR_scratch (s₀ : State) : stR (kA s₀ 3) = R (kA s₀) 3 0 200 := by
  simp only [stR, R, ptr_zero]

/-- The writes of row `i` miss the third state. -/
theorem row_st {s₀ : State} (hp : Pre P s₀) (i : Nat) (hi : i < P.k) :
    ∀ q ∈ rowWrites P s₀ i, (stR (kA s₀ 3)).Disjoint q := by
  have hw := hp.wf
  intro q hq
  rw [stR_scratch]
  simp only [rowWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inr (.inl (by lom)))
  · exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))
  · exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))

/-- The writes of row `i` lie in the written arguments. -/
theorem row_wr {s₀ s : State} (hp : Pre P s₀) (hk : KB P s₀ s) (i : Nat) (hi : i < P.k) :
    ∀ q ∈ rowWrites P s₀ i, ∃ q' ∈ s.wr, Region.Sub q q' := by
  have hw := hp.wf
  intro q hq
  rw [hk.wr, hp.wr]
  simp only [rowWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨⟨kA s₀ 3, kL P 3⟩, by simp, R.sub (by kl)⟩
  · exact ⟨⟨kA s₀ 1, kL P 1⟩, by simp, R.sub (by kl)⟩
  · exact ⟨⟨kA s₀ 2, kL P 2⟩, by simp, R.sub (by kl)⟩

/-- **A row of `t̂`**, once the matrix holds its entries. -/
theorem row_step {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) {n r h : Nat}
    (hrk : r < P.k) (hn : P.k * (r + 1) ≤ n) (H : IL P s₀ n r h s) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgRow P r) s (IL P s₀ n (r + 1) h) := by
  have hw := hp.wf
  have kb := H.b.kb
  have tl : TLW P s₀ s.mem (s.gpr .x24) n r s :=
    ⟨⟨kb, H.b.rho, H.b.sig, rfl, H.le, fun e he => ⟨H.b.red e he, rfl⟩⟩, H.sp, H.dk, H.rows⟩
  have rt := readonly_rows hp kb H.tables.gamma H.tables.gammaRead H.tables.gammaApart
  have ha : (polyRegion (s.gpr .x28 + BitVec.ofNat 64 (TP P))).Disjoint
      ⟨s.syms "VG_MLKEM_GAMMA", 512⟩ := by
    rw [kb.x28]
    exact (rt.apart r hrk _ (by simp [rowWrites])).symm
  refine WP.mono_syms (fused_row_readyW hp hr hrk hn tl H.errors rt.table rt.read ha)
    fun t ⟨tlt, et, ft⟩ hs => ?_
  have kbt := tlt.c.kb
  have entries : ∀ e < n, polyAtW 16 t.mem (AR s₀ e) = polyAtW 16 s.mem (AR s₀ e) :=
    fun e he => (tlt.c.ahat e he).2
  have hek : 136 * h ≤ kL P 1 := by
    have := Nat.mul_le_mul_left 384 H.rk
    have := H.hr
    have := hw.facts
    simp only [kL]; lom
  have hek' : 136 * h ≤ P.ekLen := hek
  have hek0 : 0 + 136 * h ≤ kL P 1 := by omega_using [hek]
  have hhr := H.hr
  refine ⟨⟨kbt, tlt.c.rho, tlt.c.sig, by rw [tlt.c.x24]; exact H.b.acc, fun e he => (tlt.c.ahat e he).1,
    fun e he => ?_⟩, tlt.sp, et, tlt.dk, ?_, hn, H.le, by omega_using [hrk], ?_, by omega_using [hhr], ?_,
    H.tstk.of hs (by rw [kbt.sp, kb.sp])⟩
  · have r₀ := H.b.res e he
    simp only [aAtW, cw, ite_true] at r₀ ⊢
    rw [show kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e) = AR s₀ e from rfl, entries e he]
    exact r₀
  · intro i' hi'
    have hrow : P.k * (i' + 1) ≤ n :=
      Nat.le_trans (Nat.mul_le_mul_left P.k (show i' + 1 ≤ r + 1 by omega_using [hi'])) hn
    rw [tVW_congr (m := t.mem) (m' := s.mem) fun j hj => entries _ (lt_row hrow hj)]
    exact tlt.ek i' hi'
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame ft (row_st hp r hrk), H.hash]
    refine hstate_prefix hek' ?_
    have e1 : kA s₀ 1 = kA s₀ 1 + BitVec.ofNat 64 0 := (ptr_zero _).symm
    rw [e1, bytesAt_frame ft (fun q hq => ?_) (by have := kL_le hw 1; omega_using [hek, this])]
    simp only [rowWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (by decide) (by decide) hek0 (by kl) (.inl (by decide))
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (by decide) (by decide) hek0 (by kl)
        (.inr (.inl (by have := H.hr; omega_using [hhr])))
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (by decide) (by decide) hek0 (by kl) (.inl (by decide))
  · exact H.tables.frame hs (by rw [kbt.rd, kb.rd]) (by rw [kbt.wr, kb.wr]) (by rw [kbt.sp, kb.sp])
      (ft.sub (row_wr hp kb r hrk))

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! # The pairs of the matrix between the rows of `t̂`

`pair_step`: a pair of the matrix (`Hybrid.pairM` in key generation's
workspace) whose first `m` main squeezes absorb blocks `h`, …, `h + m - 1` of
`ek`, all of them already encoded (`136 (h + m) ≤ 384 r`), keeps the interleaved
invariant `IL`. `last_step`: the final entry of an odd matrix. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Hybrid (TStk frame)

variable {P : KemLay}

/-- `ek` is a message the third state can absorb. -/
theorem srcOkK (hw : P.Wf) : Hybrid.SrcOk (Impl.MlKem.AArch64.Kem16.kgSrc P) := by
  have := hw.facts
  refine ⟨.inr (.inl rfl), ?_, rfl, ?_⟩ <;>
    simp only [Impl.MlKem.AArch64.Kem16.kgSrc, KemLay.ekLen] <;> omega_arith

/-- What a hashing pair of key generation writes. -/
abbrev pairWritesH (s₀ : State) (e : Nat) : List Region :=
  Hybrid.pairWrites3 (kA s₀ 3+BitVec.ofNat 64 SS) (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
    (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) (kA s₀ 3) s₀.sp

theorem pairH_far {s₀ : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e : Nat} (he : e+1<P.k*P.k)
    {b o l : Nat} (hb : b<4) (hf : o+l≤kL P b)
    (hs : b≠3 ∨ ((o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤AH+1024*e ∨ AH+1024*(e+2)≤o) ∧ 200 ≤ o)) :
    ∀ r ∈ pairWritesH s₀ e, (R (kA s₀) b o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pair_far hp he hb hf (by rcases hs with hs | hs; exacts [.inl hs, .inr ⟨hs.1, hs.2.1⟩]) r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [stR_scratch]
      exact hp.args.rdisj hb (by decide) hf (by kl) (by rcases hs with hs | hs <;> omega_arith)
    · exact (hk.R hb hf).symm

theorem pairH_kb {s₀ s t : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (ht : Keep Paired.pairRegs s t) (hf : Frame (pairWritesH s₀ e) s.mem t.mem) :
    KB P s₀ t := by
  have hw := hp.wf
  obtain h1 := pairH_far hp hk he (b:=3) (o:=SV P) (l:=48) (by decide) hp.sv (.inr ⟨.inr (by lom), .inr (by lom), by lom⟩)
  obtain h2 := pairH_far hp hk he (b:=0) (o:=0) (l:=64) (by decide) (by kl) (.inl (by decide))
  exact h.frame ht hf (by decide) fun r hr => ⟨h1 r hr, h2 r hr⟩

theorem BInvW.pairedH {s₀ s t : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : BInvW true P s₀ e s) {S : Impl.MlKem.AArch64.Hybrid.HSrc} {ea : Addr} {E : List Byte} {j m : Nat}
    (ht : Hybrid.PairMOutcomeW true S (matSeed (rhoK P s₀) (e/P.k) (e%P.k))
      (matSeed (rhoK P s₀) ((e+1)/P.k) ((e+1)%P.k))
      (kA s₀ 3+BitVec.ofNat 64 SS) (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) ea (kA s₀ 3) E j m s t) :
    BInvW true P s₀ (e+2) t := by
  have hw := hp.wf
  obtain fr : Frame (pairWritesH s₀ e) s.mem t.mem := by
    obtain f := ht.frame; rw [h.kb.sp] at f; exact f
  have old {i : Nat} (hi : i<e) := pairH_far hp hk he (b:=3) (o:=AH+1024*i) (l:=1024)
    (by decide) (by simp only [kL]; lom) (.inr ⟨.inr (by lom), .inl (by lom), by lom⟩)
  refine ⟨pairH_kb hp hk he h.kb ht.keep fr,?_,?_,?_,?_,?_⟩
  · rw [bytesAt_frame fr (pairH_far hp hk he (by decide) (by kl) (.inr ⟨.inl (by lom), .inl (by lom), by lom⟩))
      (by decide)]
    exact h.rho
  · rw [bytesAt_frame fr (pairH_far hp hk he (by decide) (by kl) (.inr ⟨.inl (by lom), .inl (by lom), by lom⟩))
      (by decide)]
    exact h.sig
  · have hall : allOk P s₀ (e+2) ↔ (allOk P s₀ e ∧
        (sampleNTT 280 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))).isSome) ∧
        (sampleNTT 280 (matSeed (rhoK P s₀) ((e+1)/P.k) ((e+1)%P.k))).isSome := by
      rw [show e+2=(e+1)+1 by omega_arith,allOk_succ,allOk_succ]
    rw [ht.status,h.acc]
    by_cases ha : allOk P s₀ e <;>
      by_cases hb : (sampleNTT 280 (matSeed (rhoK P s₀) (e/P.k) (e%P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed (rhoK P s₀) ((e+1)/P.k) ((e+1)%P.k))).isSome <;>
      simp [hall,ha,hb,hc]
  · intro i hi
    rcases (by omega_arith : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro i hi
    rcases (by omega_arith : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · rw [aAtW,polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.left
    · exact ht.right

theorem ekR (s₀ : State) : (⟨kA s₀ 1, P.ekLen⟩ : Region) = R (kA s₀) 1 0 (kL P 1) := by
  simp only [R, ptr_zero, kL]

/-- What a hashing pair of key generation needs of `ek`, the third state and the frame. -/
theorem hash_inputK {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (tk : TStk s) (mt : MatrixTable P s₀ s) :
    Hybrid.HashInput (Impl.MlKem.AArch64.Kem16.kgSrc P) (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1)))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") (kA s₀ 1) (kA s₀ 3) s := by
  have hw := hp.wf
  obtain f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw (by omega_arith)
  obtain f2 : AH+1024*(e+1)+1024≤kL P 3 := matrixEntry_fit hw he
  obtain ek : (⟨kA s₀ 1, (Impl.MlKem.AArch64.Kem16.kgSrc P).len⟩ : Region) = R (kA s₀) 1 0 (kL P 1) := ekR s₀
  have pR : (⟨kA s₀ 3+BitVec.ofNat 64 SS, 2048⟩ : Region) = R (kA s₀) 3 SS 2048 := rfl
  have aR : polyRegion (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) = R (kA s₀) 3 (AH+1024*e) 1024 := rfl
  have bR : polyRegion (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) = R (kA s₀) 3 (AH+1024*(e+1)) 1024 := rfl
  obtain fS : 0 + 200 ≤ kL P 3 := by
    show 0 + 200 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  obtain fP : KG.SS + 2048 ≤ kL P 3 := by
    show 1056 + 2048 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  obtain fE : 0 + kL P 1 ≤ kL P 1 := by omega_arith
  refine ⟨⟨cov_w hp h (b := 3) (o := SS) (l := 2048) (by decide) fP, ?_, ?_,
    by rw [h.sp]; exact hk.sp, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, h.x28, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stR_scratch]; exact cov_w hp h (b := 3) (o := 0) (l := 200) (by decide) fS
  · rw [ek]; exact cov_r hp h (b := 1) (o := 0) (l := kL P 1) (by decide) fE
  · rw [stR_scratch, pR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := 0) (l₁ := 200) (b₂ := 3) (o₂ := SS) (l₂ := 2048)
      (by decide) (by decide) fS fP (.inr (.inl (by decide)))
  · rw [stR_scratch, ek]
    exact hp.args.rdisj (b₁ := 3) (o₁ := 0) (l₁ := 200) (b₂ := 1) (o₂ := 0) (l₂ := kL P 1)
      (by decide) (by decide) fS fE (.inl (by decide))
  · rw [ek, pR]
    exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (l₁ := kL P 1) (b₂ := 3) (o₂ := SS) (l₂ := 2048)
      (by decide) (by decide) fE fP (.inl (by decide))
  · rw [h.sp, pR]; exact hk.R (b := 3) (o := SS) (l := 2048) (by decide) fP
  · rw [h.sp, stR_scratch]; exact hk.R (b := 3) (o := 0) (l := 200) (by decide) fS
  · rw [h.sp, ek]; exact hk.R (b := 1) (o := 0) (l := kL P 1) (by decide) fE
  · show s.gpr .x26 + BitVec.ofNat 64 0 = kA s₀ 1
    rw [h.x26, ptr_zero]
  · rw [stR_scratch]; exact mt.apart.sub_right (R.sub fS)
  · rw [h.sp]; have t := tk.shuffle; rw [h.sp] at t; exact t
  · rw [stR_scratch, aR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := AH+1024*e) (l₁ := 1024) (b₂ := 3) (o₂ := 0) (l₂ := 200)
      (by decide) (by decide) f1 fS (.inr (.inr (by lom)))
  · rw [stR_scratch, bR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := AH+1024*(e+1)) (l₁ := 1024) (b₂ := 3) (o₂ := 0) (l₂ := 200)
      (by decide) (by decide) f2 fS (.inr (.inr (by lom)))
  · rw [ek, aR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := AH+1024*e) (l₁ := 1024) (b₂ := 1) (o₂ := 0) (l₂ := kL P 1)
      (by decide) (by decide) f1 fE (.inl (by decide))
  · rw [ek, bR]
    exact hp.args.rdisj (b₁ := 3) (o₁ := AH+1024*(e+1)) (l₁ := 1024) (b₂ := 1) (o₂ := 0) (l₂ := kL P 1)
      (by decide) (by decide) f2 fE (.inl (by decide))

/-- The rejection table, from the constant tables. -/
theorem matrixTable_of {s₀ s : State} (hp : Pre P s₀) (h : KB P s₀ s) (ta : Tables s) : MatrixTable P s₀ s := by
  obtain scratch : Covers [⟨kA s₀ 3, P.scl⟩] s.wr := by
    simpa only [R, ptr_zero] using cov_w hp h (b := 3) (o := 0) (l := P.scl) (by decide) (by kl)
  exact ⟨ta.shuffle, ta.shuffleRead, apart_of_covers ta.shuffleApart scratch⟩

/-- The writes of a hashing pair lie in `scratch` and the frame. -/
theorem pairH_wr {s₀ s : State} (hp : Pre P s₀) (hk : KB P s₀ s) {e : Nat} (he : e+1<P.k*P.k) :
    ∀ q ∈ pairWritesH s₀ e, ∃ q' ∈ s.wr ++ [frame s.sp], Region.Sub q q' := by
  have hw := hp.wf
  obtain f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw (by omega_arith)
  obtain f2 : AH+1024*(e+1)+1024≤kL P 3 := matrixEntry_fit hw he
  obtain fS : 0 + 200 ≤ kL P 3 := by
    show 0 + 200 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  obtain fP : KG.SS + 2048 ≤ kL P 3 := by
    show 1056 + 2048 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  obtain sc : (⟨kA s₀ 3, kL P 3⟩ : Region) ∈ s.wr ++ [frame s.sp] := by rw [hk.wr, hp.wr]; simp
  intro q hq
  simp only [pairWritesH, Hybrid.pairWrites3, Paired.stepWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with (rfl | rfl | rfl) | rfl | rfl
  · exact ⟨_, sc, R.sub (A := kA s₀) (b := 3) (o := SS) (l := 2048) fP⟩
  · exact ⟨_, sc, R.sub (A := kA s₀) (b := 3) (o := AH+1024*e) (l := 1024) f1⟩
  · exact ⟨_, sc, R.sub (A := kA s₀) (b := 3) (o := AH+1024*(e+1)) (l := 1024) f2⟩
  · exact ⟨_, sc, by rw [stR_scratch]; exact R.sub fS⟩
  · exact ⟨_, List.mem_append_right _ (by rw [hk.sp]; exact List.mem_singleton_self _), fun _ h => h⟩

/-- **A hashing pair** of the matrix, between the rows of `t̂`. -/
theorem pair_step {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P) {p r h m : Nat}
    (he : 2*p+1 < P.k*P.k) (hm : m ≤ 3) (hb : ∀ k < m, 136*(h+k) < P.ekLen) (hhr : 136*(h+m) ≤ 384*r)
    (H : IL P s₀ (2*p) r h s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.pairM sha3 SB SS AH P (Impl.MlKem.AArch64.Kem16.kgSrc P) (2*p) h m true) s
      (IL P s₀ (2*p+2) r (h+m)) := by
  have hw := hp.wf
  have kb := H.b.kb
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  obtain hoa : AH+1024*(2*p)<65536 := by simp only [KG.AH]; omega_arith
  obtain hob : AH+1024*(2*p+1)<65536 := by simp only [KG.AH]; omega_arith
  obtain hk1 : 0 < P.k := by omega_arith
  obtain hk2 : P.k ≤ 256 := by omega_arith
  obtain mt := matrixTable_of hp kb H.tables
  obtain pin := pair_input hp he kb mt
  obtain hin := hash_inputK hp hk he kb H.tstk mt
  rw [Hybrid.pairM_iff]
  refine WP.mono_syms (Hybrid.pairMCode_ok (sha3 := sha3) P (Impl.MlKem.AArch64.Kem16.kgSrc P) (a := 2*p) (j := h) (m := m)
    (srcOkK hw) (by decide) (by decide) (by decide) hoa hob pin hin (fun k hk _ => hb k hk) H.hash rfl
    (by rw [H.b.acc]; split; exacts [Or.inr rfl, Or.inl rfl])) fun t ht sy => ?_
  obtain post := ht.outcome (p := kA s₀ 3+BitVec.ofNat 64 SS) hk1 hk2
  simp only [Paired.seedBytes, H.b.rho] at post
  obtain fr : Frame (pairWritesH s₀ (2*p)) s.mem t.mem := by
    obtain f := post.frame; rw [kb.sp] at f; exact f
  obtain bt := BInvW.pairedH hp hk he H.b post
  have kbt := bt.kb
  have hrn := H.rn
  have hrk := H.rk
  have far {o l : Nat} (hf : o+l≤kL P 3) (hs : AH + 1024 * (P.k * P.k) ≤ o) :=
    pairH_far hp hk he (b := 3) (o := o) (l := l) (by decide) hf (.inr ⟨.inr (by lom), .inr (by omega_arith), by lom⟩)
  refine ⟨bt, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, by omega_arith, by omega_arith, H.rk, ?_, hhr, ?_,
    H.tstk.of sy (by rw [kbt.sp, kb.sp])⟩
  · exact polyIsW_frame_poly (w16 := true) fr (far (by kl) (by lom)) (H.sp j hj)
  · exact polyIsW_frame_poly (w16 := true) fr (far (Noise.noise_fits hr hj)
      (by have := Noise.noise_past_kg hr j; lom))
      (H.errors j hj)
  · rw [bytesAt_frame fr (pairH_far hp hk he (by decide) (by kl) (.inl (by decide))) (by decide)]
    exact H.dk j hj
  · refine IL.rowsDone_frame H.rn H.rows fr (fun e' he' q hq => ?_) (fun i' hi' q hq =>
      ⟨pairH_far hp hk he (by decide) (by kl) (.inl (by decide)) q hq,
        pairH_far hp hk he (by decide) (by kl) (.inl (by decide)) q hq⟩)
    exact pairH_far hp hk he (b := 3) (o := AH+1024*e') (l := 1024) (by decide) (by simp only [kL]; lom)
      (.inr ⟨.inr (by lom), .inl (by lom), by lom⟩) q hq
  · rw [post.hash, ← post.ek, Nat.min_eq_right hm]; rfl
  · exact Hybrid.tables_frame128 H.tables H.tstk sy post.keep.rd post.keep.wr post.keep.sp
      (fr.sub (pairH_wr hp kb (by omega_arith)))

/-- The last entry of the matrix, with what it writes. -/
theorem matrix_singletonF {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : BInvW true P s₀ e s) (tb : MatrixTable P s₀ s) :
    WP isa (Paired.lastCode sha3 SB SS e P.k (AH+1024*e) true) s fun t =>
      BInvW true P s₀ (e+1) t ∧ Frame (lastWrites s₀ e) s.mem t.mem ∧ Keep Paired.pairRegs s t ∧
        t.syms = s.syms := by
  have hw := hp.wf
  obtain f0 : SS+2048≤kL P 3 := by kl
  obtain f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw he
  obtain ctx := singleton_context hp he h.kb tb
  refine WP.mono_syms (Paired.lastCode_ok (sha3 := sha3) (sb:=SB) (ss:=SS) (a:=e) (k:=P.k) (off:=AH+1024*e)
    (p:=kA s₀ 3+BitVec.ofNat 64 SS) (seed:=kA s₀ 3+BitVec.ofNat 64 SB)
    (out:=kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
    (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    (by rw [h.kb.x28]) (by rw [h.kb.x28]) (by rw [h.kb.x28])
    (by
      intro j hj
      rw [ptr_add]
      exact in_R (cov_r hp h.kb (b:=3) (o:=SB) (l:=32) (by decide) (by kl))
        (k:=8*j) (by omega_arith) (by omega_arith))
    (hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=SS) (l₂:=2048)
      (by decide) (by decide) (by kl) f0 (by decide))
    (hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=AH+1024*e) (l₂:=1024)
      (by decide) (by decide) (by kl) f1 (by lom)) ctx rfl
    (by
      rw [h.acc]
      by_cases hh : allOk P s₀ e
      · rw [ite_eq_left hh]; exact Or.inr rfl
      · rw [ite_eq_right hh]; exact Or.inl rfl)) fun t ht sy=>?_
  have out := ht.outcome
  simp only [Paired.seedBytes,h.rho] at out
  exact ⟨h.singleton hp he out, out.frame, out.keep, sy⟩

/-- **The final entry** of an odd matrix, between the rows of `t̂`. -/
theorem last_step {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) {r h : Nat}
    (hodd : P.k * P.k % 2 = 1) (H : IL P s₀ (P.k * P.k - 1) r h s) :
    WP isa (Paired.lastSample sha3 P true true) s (IL P s₀ (P.k * P.k) r h) := by
  have hw := hp.wf
  have kb := H.b.kb
  obtain hk1 : 0 < P.k * P.k := by omega_arith
  obtain he : P.k * P.k - 1 < P.k * P.k := by omega_arith
  have hrn := H.rn
  have hrk := H.rk
  rw [Paired.lastSample_eq]
  simp only [ite_true]
  refine WP.mono (matrix_singletonF (sha3 := sha3) hp he H.b (matrixTable_of hp kb H.tables))
    fun t ⟨bt, fr, kt, sy⟩ => ?_
  rw [Nat.sub_add_cancel hk1] at bt
  have kbt := bt.kb
  have far {o l : Nat} (hf : o+l≤kL P 3) (hs : AH + 1024 * (P.k * P.k) ≤ o) :=
    last_far hp he (b := 3) (o := o) (l := l) (by decide) hf (.inr ⟨.inr (by lom), .inr (by omega_arith)⟩)
  obtain fS : 0 + 200 ≤ kL P 3 := by
    show 0 + 200 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  refine ⟨bt, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, by omega_arith, Nat.le_refl _, H.rk, ?_, H.hr, ?_,
    H.tstk.of sy (by rw [kbt.sp, kb.sp])⟩
  · exact polyIsW_frame_poly (w16 := true) fr (far (by kl) (by lom)) (H.sp j hj)
  · exact polyIsW_frame_poly (w16 := true) fr (far (Noise.noise_fits hr hj)
      (by have := Noise.noise_past_kg hr j; lom)) (H.errors j hj)
  · rw [bytesAt_frame fr (last_far hp he (by decide) (by kl) (.inl (by decide))) (by decide)]
    exact H.dk j hj
  · refine IL.rowsDone_frame H.rn H.rows fr (fun e' he' q hq => ?_) (fun i' hi' q hq =>
      ⟨last_far hp he (by decide) (by kl) (.inl (by decide)) q hq,
        last_far hp he (by decide) (by kl) (.inl (by decide)) q hq⟩)
    exact last_far hp he (b := 3) (o := AH+1024*e') (l := 1024) (by decide) (by simp only [kL]; lom)
      (.inr ⟨.inr (by lom), .inl (by lom)⟩) q hq
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fr (fun q hq => by
      rw [stR_scratch]; exact last_far hp he (b := 3) (o := 0) (l := 200) (by decide) fS
        (.inr ⟨.inl (by lom), .inl (by lom)⟩) q hq), H.hash]
    rw [show kA s₀ 1 = kA s₀ 1 + BitVec.ofNat 64 0 from (ptr_zero _).symm,
      bytesAt_frame (p := kA s₀ 1 + BitVec.ofNat 64 0) (len := P.ekLen) fr
        (last_far hp he (b := 1) (o := 0) (l := kL P 1) (by decide) (by omega_arith) (.inl (by decide)))
        (by have := kL_le hw 1; simp only [kL] at this; omega_arith)]
  · exact H.tables.frame sy kt.rd kt.wr kt.sp (fr.sub fun q hq => by
      rw [kb.wr, hp.wr]
      simp only [lastWrites, Paired.fullWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨⟨kA s₀ 3, kL P 3⟩, by simp, R.sub (A := kA s₀) (b := 3) (o := SS) (l := 2048) (by kl)⟩
      · exact ⟨⟨kA s₀ 3, kL P 3⟩, by simp, R.sub (A := kA s₀) (b := 3) (o := AH+1024*(P.k*P.k-1)) (l := 1024)
          (matrixEntry_fit hw he)⟩)

end VG.Proof.MlKem.AArch64.KeyGen
