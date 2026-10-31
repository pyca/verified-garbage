module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHints
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- Short-circuiting fused pairs retain the same prefix invariant as single
checks, advancing it by two and using one single check for an odd tail. -/
theorem earlyPairedSeq_ok {one two : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat),
      (∀ k, a≤k → k<a+n → ∀ s, I k s → WP isa (one k) s (I (k+1))) →
      (∀ k, a≤k → k+1<a+n → ∀ s, I k s → WP isa (two k) s (I (k+2))) →
      ∀ s, I a s → WP isa (Impl.MlDsa.AArch64.Sign.Optimized.seqPairedOk one two a n) s
        fun u => ∃ k, a≤k ∧ k≤a+n ∧ I k u ∧ (k=a+n ∨ (u.gpr .x24).setWidth 32=0)
  | 0,a,_,_,s,h => WP.block_nil ⟨a,Nat.le_refl _,by omega,h,.inl (by omega)⟩
  | 1,a,h,_,s,hs => WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun u hu =>
      ⟨a+1,by omega,by omega,hu,.inl rfl⟩
  | n+2,a,h1,h2,s,hs => by
    rw [Impl.MlDsa.AArch64.Sign.Optimized.seqPairedOk]
    refine WP.seq (WP.mono (h2 a (Nat.le_refl _) (by omega) s hs) fun u hu => ?_)
    refine ifOkElse_ok (fun _ => ?_) (fun hz => ?_)
    · refine WP.mono (earlyPairedSeq_ok n (a+2)
        (fun k hk hk' => h1 k (by omega) (by omega))
        (fun k hk hk' => h2 k (by omega) (by omega)) u hu) ?_
      rintro v ⟨k,hk,hk',hi,hd⟩
      exact ⟨k,by omega,by omega,hi,hd.imp (fun _ => by omega) id⟩
    · exact WP.block_nil ⟨a+2,by omega,by omega,hu,.inr hz⟩

theorem earlyZ_step {p:Params} {S:Nat} {σ s:State} {t r:Nat}
    (hp:Ok3 p) (h16:16≤S) (hS:S<2^64) (hr:r<p.ℓ)
    (h:PositiveIZ p S σ t r s ∧ PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zR p r) s
      fun u=>PositiveIZ p S σ t (r+1) u ∧ PairedRoots S u := by
  have hd:(Impl.MlDsa.AArch64.Sign.Optimized.zR p r).aarch64Depth=0:=by rfl
  exact WP.pairedRoots (optimizedZ_ok hp hr h.1) h.2 (by rw [hd];omega) hS

theorem earlyR0_step {p:Params} {S:Nat} {σ s:State} {t r:Nat}
    (hp:Ok3 p) (h16:16≤S) (hS:S<2^64) (hr:r<p.k)
    (h:PositiveIR p S σ t r s ∧ PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.r0R p r) s
      fun u=>PositiveIR p S σ t (r+1) u ∧ PairedRoots S u := by
  have hd:(Impl.MlDsa.AArch64.Sign.Optimized.r0R p r).aarch64Depth=0:=by rfl
  exact WP.pairedRoots (optimizedR0_ok hp hr h.1) h.2 (by rw [hd];omega) hS

theorem PositiveIZ.done {p:Params} {S:Nat} {σ s:State} {t k:Nat}
    (hk:k≤p.ℓ) (h:PositiveIZ p S σ t k s) (hd:k=p.ℓ ∨ (s.gpr .x24).setWidth 32=0) :
    s.gpr .x24=bit (ZOk p σ (p.ℓ*t)) := by
  rcases hd with rfl|hz
  · exact h.2
  · rw [h.2] at hz ⊢
    have hn:¬∀j<k,normRq [Zv p σ (p.ℓ*t) j]<p.γ₁-p.β:=fun ha=>(bit_ne.mpr ha) hz
    rw [bit_zero.mpr hn,bit_zero.mpr (fun ha=>hn fun j hj=>ha j (by omega))]

theorem PositiveIR.done {p:Params} {S:Nat} {σ s:State} {t k:Nat}
    (hk:k≤p.k) (h:PositiveIR p S σ t k s) (hd:k=p.k ∨ (s.gpr .x24).setWidth 32=0) :
    s.gpr .x24=bit (ZOk p σ (p.ℓ*t) ∧ R0Ok p σ (p.ℓ*t)) := by
  rcases hd with rfl|hz
  · exact h.2
  · rw [h.2] at hz ⊢
    have hn:¬(ZOk p σ (p.ℓ*t) ∧ ∀j<k,normRq [R0v p σ (p.ℓ*t) j]<p.γ₂-p.β):=fun ha=>(bit_ne.mpr ha) hz
    rw [bit_zero.mpr hn,bit_zero.mpr (fun ha=>hn ⟨ha.1,fun j hj=>ha.2 j (by omega)⟩)]

theorem positivePairedChecks_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (h16 : 16≤S) (hS : S<2^64)
    (roots : PairedRoots S s) (h : PositiveIB p S σ t s)
    (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) s fun u=>
      (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks
  refine WP.seq (WP.seq (WP.mono (positivePairedChallenge_ok hp h16 roots h h1) fun a ha=>?_))
  refine WP.seq (WP.mono (positivePairedChecksInit_ok hp hc ha.2 ha.1) fun b hb=>?_)
  refine WP.mono (earlyPairedSeq_ok (I:=fun r u=>PositiveIZ p S σ t r u ∧ PairedRoots S u) p.ℓ 0
    (fun r _ hr s h=>earlyZ_step hp h16 hS (by omega) h)
    (fun r _ hr s h=>optimizedZ_pair_ok hp (by omega) h.2 h.1) b hb) fun c ⟨nz,_,hnz,hz,hdz⟩=>?_
  rw [Nat.zero_add] at hnz hdz
  have zflag:=PositiveIZ.done hnz hz.1 hdz
  refine ifOkElse_ok (fun hzpass=>?_) fun hzfail=>?_
  · have he:nz=p.ℓ:=hdz.resolve_right hzpass
    subst he
    refine WP.seq (WP.mono (earlyPairedSeq_ok (I:=fun r u=>PositiveIR p S σ t r u ∧ PairedRoots S u) p.k 0
      (fun r _ hr s h=>earlyR0_step hp h16 hS (by omega) h)
      (fun r _ hr s h=>optimizedR0_pair_ok hp (by omega) h.2 h.1) c ⟨positiveIR_of_IZ hz.1,hz.2⟩)
      fun d ⟨nr,_,hnr,hr,hdr⟩=>?_)
    rw [Nat.zero_add] at hnr hdr
    have rflag:=PositiveIR.done hnr hr.1 hdr
    refine ifOkElse_ok (fun hrpass=>?_) fun hrfail=>?_
    · have he:nr=p.k:=hdr.resolve_right hrpass
      subst he
      refine WP.seq (WP.mono (optimizedHint_paired_vector_ok hp hr.2 (positiveIH_of_IR hr.1)) fun e he=>?_)
      refine WP.seq (WP.mono (WP.pairedRoots (positiveOnesOk_ok hc he.1) he.2 (Nat.zero_le _) hS) fun f hf=>?_)
      exact WP.pairedRoots (positiveKBranch_ok hp hc hf.1) hf.2 (Nat.zero_le _) hS
    · have flag : d.gpr .x24=0 := by
        rw [rflag]; exact bit_zero.mpr (fun h=>(bit_ne.mpr h) (by rw [←rflag]; exact hrfail))
      have fail : ¬ PassV p σ (p.ℓ*t) := by
        intro hpass
        exact (bit_ne.mpr (show ZOk p σ (p.ℓ*t) ∧ R0Ok p σ (p.ℓ*t) from ⟨hpass.1,hpass.2.1⟩))
          (by rw [←rflag]; exact hrfail)
      exact WP.mono (WP.pairedRoots (positiveReject_ok hp hc hr.1.1.b.l hr.1.1.b.sampled fail flag)
        hr.2 (Nat.zero_le _) hS) fun _ hu=>⟨.inr hu.1,hu.2⟩
  · have flag : c.gpr .x24=0 := by
      rw [zflag]; exact bit_zero.mpr (fun h=>(bit_ne.mpr h) (by rw [←zflag]; exact hzfail))
    have fail : ¬ PassV p σ (p.ℓ*t) := by
      intro hpass
      exact (bit_ne.mpr hpass.1) (by rw [←zflag]; exact hzfail)
    exact WP.mono (WP.pairedRoots (positiveReject_ok hp hc hz.1.1.b.l hz.1.1.b.sampled fail flag)
      hz.2 (Nat.zero_le _) hS) fun _ hu=>⟨.inr hu.1,hu.2⟩

end VG.Proof.MlDsa.AArch64.Sign
