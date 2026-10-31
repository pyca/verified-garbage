module

import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Verified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Base
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Fintype.Fin
public import VerifiedGarbage.Impl.MlDsa.AArch64.Message
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Verify
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Layout
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Entry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inv
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseLCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSelected
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSat
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.MlKem.Mem

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.SignRest
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitializationTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedSelectedTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsForget
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.SignCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsPrologue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Base
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Frag
meta import VerifiedGarbage.TCB.Code
meta import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.FrameTiming
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Sign
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Base
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitialization
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedSignSat
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsEntry
public import VerifiedGarbage.Proof.MlDsa.Sign.Iter

@[expose] public section

/-! ## SignCopyTiming -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Impl.MlDsa.AArch64.Sign

theorem restoreSecrets_tr (p : Params) :
    RelCT isa (SameIn [.x21, .x28])
      (Impl.MlDsa.AArch64.PreparedKey.Sign.restoreSecrets p) (SameIn [.x21, .x28]) := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Sign.restoreSecrets
  refine RelCT.seq (R := SameIn [.x21, .x28]) ?_
    (RelCT.seq (R := SameIn [.x21, .x28]) ?_ ?_)
  · exact seqR_tr (Q := fun _ => SameIn [.x21, .x28]) p.ℓ 0
      (fun _ _ _ => copy_cache_tr _ _)
  · exact seqR_tr (Q := fun _ => SameIn [.x21, .x28]) p.k 0
      (fun _ _ _ => copy_cache_tr _ _)
  · exact seqR_tr (Q := fun _ => SameIn [.x21, .x28]) p.k 0
      (fun _ _ _ => copy_cache_tr _ _)

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignInitTiming -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

def CachedIM (p : Params) (S : Nat) (σ s : State) : Prop :=
  IM p S σ s ∧ StaticRoots S s ∧ (s.gpr .x22 ≠ 0 → SecretCache p S σ s)

def CachedInitRel (p : Params) (S : Nat) (E : State → State → Prop) (x y : State) : Prop :=
  RootRS p S E (CachedIM p S) x y ∧ SameIn [.x21, .x22] x y

theorem initialization_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {E : State → State → Prop} :
    RelCT isa (CachedInitRel p S E)
      (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization keccak.callee P p)
      (RootRS p S E (PositiveIK p S)) := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Sign.initialization
  refine RelCT.ite ?_ ?_ ?_
  · intro x y h
    have he := h.2.1 .x22 (by simp)
    change some (x.gpr .x22 != 0) = some (y.gpr .x22 != 0)
    rw [he]
  · refine RelCT.seq (R := RootRS p S E (PositiveID p S · p.ℓ p.k p.k)) ?_ ?_
    · intro x y tx ty x' y' h ex ey
      obtain ⟨⟨hr, hm⟩, hflag⟩ := h
      obtain ⟨σ, τ, hs, ht, hpub, he, hx, hy⟩ := hr.1
      have hxflag : x.gpr .x22 ≠ 0 := by
        change some (x.gpr .x22 != 0) = some true at hflag
        exact bne_iff_ne.mp (Option.some.inj hflag)
      have hyflag : y.gpr .x22 ≠ 0 := by rw [← hm.1 .x22 (by simp)]; exact hxflag
      have layout := lrel_of hpub hx.1.st hy.1.st
      have hbases : SameIn [.x21, .x28] x y := by
        refine ⟨fun r hr' => ?_, layout.sp⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · exact hm.1 .x21 (by simp)
        · exact layout.regs .x28 (by decide)
      have trace := (restoreSecrets_tr p _ _ _ _ _ _ hbases ex ey).1
      obtain ⟨_, u, eu, hu⟩ := restoreSecrets_ok (dChk_ok hp)
        ⟨hx.1, hx.2.1, by simp [PosFam], by simp [PosFam], by simp [PosFam]⟩ (hx.2.2 hxflag)
      obtain ⟨_, v, ev, hv⟩ := restoreSecrets_ok (dChk_ok hp)
        ⟨hy.1, hy.2.1, by simp [PosFam], by simp [PosFam], by simp [PosFam]⟩ (hy.2.2 hyflag)
      obtain ⟨_, rfl⟩ := Exec.det ex eu
      obtain ⟨_, rfl⟩ := Exec.det ey ev
      exact ⟨trace, ⟨σ, τ, hs, ht, hpub, he, hu.1, hv.1⟩, by
        simpa only [RootSymbolsEq, VG.AArch64.Exec.syms ex, VG.AArch64.Exec.syms ey] using hr.2⟩
    · apply liftRootT (fun _ _ h => ⟨h.im.st, h.roots⟩)
        (fun _ _ _ h => positiveSeed_ok hP hp h)
      exact vector_lrel_tr (fun _ _ h => h.1) keccak.mldsaSignDecodeTaint.choose_spec
  · apply RelCT.mono (positiveInitialization_tr hP hp)
    · intro x y h
      exact ⟨h.1.1.1.mono (fun _ _ he => he) (fun _ _ hi => ⟨hi.1, hi.2.1⟩), h.1.1.2⟩
    · intro _ _ h; exact h

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignRestTiming -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Sign

theorem selectedLoop_tr (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) :
    RelCT isa (PairedRS p 16 (LeakEq p 0) (PositiveIK p 16))
      (selectedLoop v p) (PositiveOX p 16) := by
  unfold selectedLoop
  split
  · rename_i hpair
    simp only [Bool.and_eq_true] at hpair
    have hk : p.k ≠ 4 := bne_iff_ne.mp hpair.2
    have hp' : p = mlDsa65 ∨ p = mlDsa87 := by
      rcases hp with h44 | h65 | h87
      · subst p; exact absurd rfl hk
      · exact .inl h65
      · exact .inr h87
    apply Cached.signLoop_tr (prims_okWith (keccak := v)) hp' (by decide)
    · have hd := (Message.cachedCommit_dle v hp').le
      change 16 * _ ≤ 16
      omega
    · have hd := (Message.pairedBall_dle v p).le
      change 16 * _ ≤ 16
      omega
  · exact selectedPairedSignLoop_tr v hp

theorem afterInitialization_tr (v : VG.Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) :
    RelCT isa (PairedRS p 16 (LeakEq p 0) (PositiveIK p 16))
      (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p)))
      (RootRS p 16 (LeakEq p 0) (FS p 16)) := by
  refine liftPairedForgetR
    (fun _ _ _ h rp => afterInitialization_ok v hp h rp) ?_
  refine RelCT.seq (selectedLoop_tr v hp) ?_
  unfold ifOk
  refine ifOkElse_tr (fun x y h => by rw [h.2.1])
    (RelCT.mono (optimizedOutput_tr (prims_okWith (keccak := v)) hp
      (lo := -(q : Int) + 1) (hi := (q : Int) - 1) (by omega) (by omega)
      (E := fun _ _ => True)) ?_ (fun _ _ h => h))
    (RelCT.mono nil_tr (fun _ _ h => h) (fun _ _ _ => trivial))
  rintro x y ⟨⟨⟨⟨σ, τ, ps, pt, pub, _, hx, hy⟩, _⟩, eq, hj⟩, hne⟩
  have ex := x24_one hx.r01 hne
  have ey : y.gpr .x24 = 1 := eq ▸ ex
  obtain ⟨_, f, fx, fy⟩ := hj ex
  exact ⟨⟨σ, τ, ps, pt, pub, trivial, hx.conversion ex, hy.conversion ey⟩, f, fx, fy⟩

def CachedPairedInitRel (p : Params) (x y : State) : Prop :=
  WithPaired 16 (CachedInitRel p 16 (LeakEq p 0)) x y

theorem rest_tr (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) :
    RelCT isa (CachedPairedInitRel p)
      (.seq (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee (primsWith v.callee) p)
        (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p))))
      (RootRS p 16 (LeakEq p 0) (FS p 16)) := by
  have hd : 16 * (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee
      (primsWith v.callee) p).aarch64Depth ≤ 16 := by
    have := (initialization_dle v p).le
    omega
  refine RelCT.seq (R := PairedRS p 16 (LeakEq p 0) (PositiveIK p 16)) ?_
    (afterInitialization_tr v hp)
  exact RelCT.mono
    (withPaired_tr hd (by decide) (initialization_tr (keccak := v) (prims_okWith (keccak := v)) hp))
    (fun _ _ h => h) (fun _ _ h => PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignPrefixTiming -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Sign

def CachedCorePre (p : Params) (s : State) : Prop :=
  (signK p 16).pre s ∧ StaticRoots 16 s ∧ (s.gpr .x22 ≠ 0 → SecretCache p 16 s s)

def CachedCorePub (p : Params) (x y : State) : Prop :=
  (signK p 16).pub x y ∧ RootSymbolsEq x y ∧ SameIn [.x21, .x22] x y

def CachedProRel (p : Params) (x y : State) : Prop :=
  RR p 16 (fun σ s => (RootedSt p 16 σ s ∧ s.gpr .x24 = 1) ∧
    (s.gpr .x22 ≠ 0 → SecretCache p 16 σ s)) RootSymbolsEq x y ∧ SameIn [.x21, .x22] x y

def CachedRARel (p : Params) (x y : State) : Prop :=
  RR p 16 (fun σ s => (IA p 16 σ (p.k * p.ℓ) s ∧ StaticRoots 16 s) ∧
    (s.gpr .x22 ≠ 0 → SecretCache p 16 σ s))
    (fun x y => x.gpr .x24 = y.gpr .x24 ∧ RootSymbolsEq x y) x y ∧ SameIn [.x21, .x22] x y

theorem cachedPro_tr {p : Params} (hp : Ok3 p) :
    RelCT isa (fun x y => CachedCorePre p x ∧ CachedCorePre p y ∧ CachedCorePub p x y)
      (.block pro) (CachedProRel p) := by
  intro x y tx ty x' y' ⟨hx, hy, pub⟩ ex ey
  have trace := positivePro_tr hp _ _ _ _ _ _
    ⟨hx.1, hy.1, pub.1, hx.2.1, hy.2.1, pub.2.1⟩ ex ey
  have wx := WP.optionalCache (rooted_prologue hp hx.1 hx.2.1) hx.2.2 (Nat.zero_le _) (by decide)
    (fun t ht => ht.1.1.top.cs .x21 (by decide))
    (fun t ht => ht.1.1.top.cs .x22 (by decide))
  have wy := WP.optionalCache (rooted_prologue hp hy.1 hy.2.1) hy.2.2 (Nat.zero_le _) (by decide)
    (fun t ht => ht.1.1.top.cs .x21 (by decide))
    (fun t ht => ht.1.1.top.cs .x22 (by decide))
  obtain ⟨_, u, eu, hu⟩ := wx
  obtain ⟨_, v, ev, hv⟩ := wy
  obtain ⟨_, rfl⟩ := Exec.det ex eu
  obtain ⟨_, rfl⟩ := Exec.det ey ev
  refine ⟨trace.1, ⟨⟨x, y, hx.1, hy.1, pub.1, hu, hv⟩, trace.2.2⟩, ?_⟩
  refine ⟨fun r hr => ?_, by rw [hu.1.1.1.top.sp, hv.1.1.1.top.sp, pub.2.2.2]⟩
  have hk : r ∈ untouched := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  rw [hu.1.1.1.top.cs r hk, hv.1.1.1.top.cs r hk, pub.2.2.1 r hr]

theorem selectedExpansion_tr (v : VG.Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) :
    RelCT isa (RR p 16 (fun σ s => RootedSt p 16 σ s ∧ s.gpr .x24 = 1) RootSymbolsEq)
      (selectedExpansion v p) (PositiveRA p 16) := by
  unfold selectedExpansion
  split
  · exact CachedMatrix.positiveExpand_tr (prims_okWith (keccak := v)) hp
  · exact positiveExpand_tr (prims_okWith (keccak := v)) hp

theorem cachedExpansion_tr (v : VG.Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) :
    RelCT isa (CachedProRel p) (selectedExpansion v p) (CachedRARel p) := by
  intro x y tx ty x' y' h ex ey
  have old := h.1.mono (fun _ _ h => h.1) (fun he => he)
  have trace := selectedExpansion_tr v hp _ _ _ _ _ _ old ex ey
  obtain ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, re⟩ := h.1
  have wx := WP.optionalCache (selectedExpansion_ok v hp (aChk_ok hp) hx.1.1 hx.1.2)
    hx.2 (selectedExpansion_depth v p) (by decide)
    (fun t ht => (ht.1.st.top.cs .x21 (by decide)).trans (hx.1.1.1.top.cs .x21 (by decide)).symm)
    (fun t ht => (ht.1.st.top.cs .x22 (by decide)).trans (hx.1.1.1.top.cs .x22 (by decide)).symm)
  have wy := WP.optionalCache (selectedExpansion_ok v hp (aChk_ok hp) hy.1.1 hy.1.2)
    hy.2 (selectedExpansion_depth v p) (by decide)
    (fun t ht => (ht.1.st.top.cs .x21 (by decide)).trans (hy.1.1.1.top.cs .x21 (by decide)).symm)
    (fun t ht => (ht.1.st.top.cs .x22 (by decide)).trans (hy.1.1.1.top.cs .x22 (by decide)).symm)
  obtain ⟨_, u, eu, hu⟩ := wx
  obtain ⟨_, w, ew, hw⟩ := wy
  obtain ⟨_, rfl⟩ := Exec.det ex eu
  obtain ⟨_, rfl⟩ := Exec.det ey ew
  refine ⟨trace.1, ⟨⟨σ, τ, ps, pt, pub, hu, hw⟩, trace.2.1.2, ?_⟩, ?_⟩
  · simpa only [RootSymbolsEq, VG.AArch64.Exec.syms ex, VG.AArch64.Exec.syms ey] using re
  · refine ⟨fun r hr => ?_, by rw [hu.1.1.st.top.sp, hw.1.1.st.top.sp,
      ← hx.1.1.1.top.sp, ← hy.1.1.1.top.sp, h.2.2]⟩
    have hk : r ∈ untouched := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [hu.1.1.st.top.cs r hk, hw.1.1.st.top.cs r hk,
      ← hx.1.1.1.top.cs r hk, ← hy.1.1.1.top.cs r hk, h.2.1 r hr]

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignCoreTiming -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Sign

theorem core_ct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) :
    ConstantTime isa (fun s => CachedCorePre p s ∧ PairedRoots 16 s)
      (fun x y => CachedCorePub p x y ∧
        x.syms "VG_MLDSA_INV_PAIR" = y.syms "VG_MLDSA_INV_PAIR")
      (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p) := by
  have trace : RelCT isa
      (WithPaired 16 (fun x y => CachedCorePre p x ∧ CachedCorePre p y ∧ CachedCorePub p x y))
      (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p)
      (fun _ _ => True) := by
    change RelCT isa _ (.seq (.block pro) (.seq (selectedExpansion v p)
      (.seq (ifOk (.seq
        (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee (primsWith v.callee) p)
        (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p)))))
        (.block epi)))) _
    refine RelCT.seq (withPaired_tr (Nat.zero_le _) (by decide) (cachedPro_tr hp))
      (RelCT.seq (withPaired_tr (selectedExpansion_depth v p) (by decide) (cachedExpansion_tr v hp)) ?_)
    refine RelCT.seq (R := LRel 16 (sgR p) (sgW p)) ?_
      (lrel_tr (fun _ _ h => h) (by taint_decide))
    unfold ifOk
    refine ifOkElse_tr (P := WithPaired 16 (CachedRARel p))
      (fun _ _ h => by rw [h.1.1.2.1])
      (RelCT.mono (rest_tr v hp) ?_ (fun _ _ h => h.1.lrel (fun _ _ h => h.st)))
      (RelCT.mono nil_tr (fun _ _ h => h) ?_)
    · rintro x y ⟨⟨⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, eq, re⟩, hm⟩, px, py, pe⟩, hne⟩
      have ex := x24_one hx.1.1.r01 hne
      have ey : y.gpr .x24 = 1 := eq ▸ ex
      obtain ⟨ox, fx⟩ := hx.1.1.ok ex
      obtain ⟨oy, fy⟩ := hy.1.1.ok ey
      exact ⟨⟨⟨⟨σ, τ, ps, pt, pub, pub_leq pub (expandA_max ox) (expandA_max oy),
        ⟨⟨hx.1.1.st, ox, fx⟩, hx.1.2, hx.2⟩,
        ⟨⟨hy.1.1.st, oy, fy⟩, hy.1.2, hy.2⟩⟩, re⟩, hm⟩, px, py, pe⟩
    · intro _ _ h
      exact h.1.1.1.lrel (fun _ _ h => h.1.1.st)
  intro x y tx ty x' y' hx hy pub ex ey
  exact (trace _ _ _ _ _ _ ⟨⟨hx.1, hy.1, pub.1⟩, hx.2, hy.2, pub.2⟩ ex ey).1

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignKernel -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign

def cachedCoreK (p : Params) : Contract isa where
  pre s := CachedCorePre p s ∧ PairedRoots 16 s
  post := (signK p 16).post
  pub x y := CachedCorePub p x y ∧
    x.syms "VG_MLDSA_INV_PAIR" = y.syms "VG_MLDSA_INV_PAIR"

theorem cachedCore_correct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    (s : State) (h : (cachedCoreK p).pre s) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p)
      s tr t ∧ abiPreserved s t ∧ (cachedCoreK p).post s t :=
  core_correct v hp s h.1.1 h.1.2.1 h.2 h.1.2.2

theorem core_trace_narrow (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {s : State} {rd wr : List Region} (hpre : (cachedCoreK p).pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    {tr : List Leak} {t : State}
    (he : Exec isa (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p) s tr t) :
    ∃ u, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p)
      (s.withRegions rd wr) tr u :=
  trace_narrow (cachedCore_correct v hp) hpre hc hw he

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignEntryTiming -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign

def signPushed (s : State) : State := pushed .x22 (pushed .x21 s)

theorem signPushed_wr_cover (s : State) : Covers s.wr (signPushed s).wr :=
  (push_wr_cover .x21 s).trans (push_wr_cover .x22 (pushed .x21 s))

theorem sign_setup_narrow {σ s : State}
    (h : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signPushed σ) s) :
    VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signInner σ) (s.withRegions σ.rd σ.wr) :=
  ⟨h.gpr, h.mem, rfl, rfl, h.sp, h.vcs⟩

def SharedSignRel (p : Params) (x y : State) : Prop :=
  (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre x ∧
  (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre y ∧
  (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pub x y

theorem setup_sign_pub {p : Params} (hp : Ok3 p) {σ τ x y : State}
    (h : SharedSignRel p σ τ)
    (hx : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signPushed σ) x)
    (hy : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signPushed τ) y)
    (x21 : x.gpr .x21 = σ.gpr .x5) (x22 : x.gpr .x22 = σ.gpr .x6)
    (y21 : y.gpr .x21 = τ.gpr .x5) (y22 : y.gpr .x22 = τ.gpr .x6)
    (xs : x.syms = σ.syms) (ys : y.syms = τ.syms) :
    (cachedCoreK p).pub (x.withRegions σ.rd σ.wr) (y.withRegions τ.rd τ.wr) := by
  have nx := setup_sign_inputs hp h.1 (sign_setup_narrow hx) x21 x22 xs
  have ny := setup_sign_inputs hp h.2.1 (sign_setup_narrow hy) y21 y22 ys
  have pub := h.2.2
  sig_pub [signWithCacheContract, signWithCacheSig, signSig, abi, argRegs,
    Abi.withConsts, pairedSignRootConsts_eq] at pub
  obtain ⟨hsp, hf, hi, hp', hb, h0, h1, h2, h3, h4, h5, h6⟩ := pub
  have esp : x.sp = y.sp := by
    rw [hx.sp, hy.sp]
    change (σ.sp - 16) - 16 = (τ.sp - 16) - 16
    rw [hsp]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, esp, ?_⟩
    · exact (hx.get .x0).trans (h0.trans (hy.get .x0).symm)
    · exact (hx.get .x1).trans (h1.trans (hy.get .x1).symm)
    · exact (hx.get .x2).trans (h2.trans (hy.get .x2).symm)
    · exact (hx.get .x3).trans (h3.trans (hy.get .x3).symm)
    · exact (hx.get .x4).trans (h4.trans (hy.get .x4).symm)
    · change signLeak p (skOf p _) (muOf _) (rndOf _) = signLeak p (skOf p _) (muOf _) (rndOf _)
      rw [nx.2.2.2.2.1, nx.2.2.2.2.2.1, nx.2.2.2.2.2.2.1,
        ny.2.2.2.2.1, ny.2.2.2.2.2.1, ny.2.2.2.2.2.2.1]
      exact hb
  · simpa only [RootSymbolsEq, State.withRegions, xs, ys] using And.intro hf hi
  · refine ⟨fun r hr => ?_, esp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact x21.trans (h5.trans y21.symm)
    · exact x22.trans (h6.trans y22.symm)
  · simpa only [State.withRegions, xs, ys] using hp'

theorem withCache_ct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) :
    ConstantTime isa (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre
      (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pub
      (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p) := by
  have hs : ∀ x y, SharedSignRel p x y → x.sp = y.sp := by
    intro x y h
    have pub := h.2.2
    sig_pub [signWithCacheContract, signWithCacheSig, signSig, abi, argRegs,
      Abi.withConsts, pairedSignRootConsts_eq] at pub
    exact pub.1
  have trace : RelCT isa (SharedSignRel p)
      (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p)
      (fun _ _ => True) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Sign.withCache
    refine frame_tr hs (frame_tr (pushRel_sp hs) (R := fun _ _ => True) ?_)
    intro a b ta tb a' b' h ex ey
    rcases h with ⟨a1, b1, ⟨σ, τ, h, rfl, rfl⟩, rfl, rfl⟩
    cases ex with
    | seq ax bx =>
      cases ey with
      | seq ay by' =>
        have pub := h.2.2
        sig_pub [signWithCacheContract, signWithCacheSig, signSig, abi, argRegs,
          Abi.withConsts, pairedSignRootConsts_eq] at pub
        obtain ⟨hsp, _, _, _, _, _, _, _, _, _, h5, h6⟩ := pub
        have ht : RelCT isa (fun x y => AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x5, .x6]) x y)
            (.block [.addImm .x .x21 .x5 0, .addImm .x .x22 .x6 0]) (fun _ _ => True) :=
          taintRel [.x5, .x6] (fun _ _ h => ⟨h.1, fun r hr => h.2 r (AArch64.Taint.mem_ofRegs.mpr hr)⟩) (by taint_decide)
        have agree : AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x5, .x6])
            (signPushed σ) (signPushed τ) := by
          refine ⟨?_, fun r hr => ?_⟩
          · change (σ.sp - 16) - 16 = (τ.sp - 16) - 16
            rw [hsp]
          · simp only [AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            exacts [h5, h6]
        have hmeta := (ht _ _ _ _ _ _ agree ax ay).1
        obtain ⟨_, x, exx, hx, x21, x22⟩ := metadata_setup (signPushed σ)
        obtain ⟨_, y, eyy, hy, y21, y22⟩ := metadata_setup (signPushed τ)
        have exeq := (Exec.det ax exx).2
        have eyeq := (Exec.det ay eyy).2
        rw [exeq] at ax bx
        rw [eyeq] at ay by'
        have xs0 := VG.AArch64.Exec.syms ax
        have xs : x.syms = σ.syms := xs0
        have ys0 := VG.AArch64.Exec.syms ay
        have ys : y.syms = τ.syms := ys0
        have nx := setup_sign_inputs hp h.1 (sign_setup_narrow hx) x21 x22 xs
        have ny := setup_sign_inputs hp h.2.1 (sign_setup_narrow hy) y21 y22 ys
        have rx : Covers (σ.rd ++ σ.wr) (x.rd ++ x.wr) := by
          rw [hx.rd, hx.wr]
          exact Covers.append (Covers.refl _) (signPushed_wr_cover σ)
        have ry : Covers (τ.rd ++ τ.wr) (y.rd ++ y.wr) := by
          rw [hy.rd, hy.wr]
          exact Covers.append (Covers.refl _) (signPushed_wr_cover τ)
        have wx : Covers σ.wr x.wr := by rw [hx.wr]; exact signPushed_wr_cover σ
        have wy : Covers τ.wr y.wr := by rw [hy.wr]; exact signPushed_wr_cover τ
        have px : (cachedCoreK p).pre (x.withRegions σ.rd σ.wr) :=
          ⟨⟨nx.1, nx.2.1, nx.2.2.2.1⟩, nx.2.2.1⟩
        have py : (cachedCoreK p).pre (y.withRegions τ.rd τ.wr) :=
          ⟨⟨ny.1, ny.2.1, ny.2.2.2.1⟩, ny.2.2.1⟩
        obtain ⟨u, eu⟩ := core_trace_narrow v hp px rx wx bx
        obtain ⟨w, ew⟩ := core_trace_narrow v hp py ry wy by'
        have hp' := setup_sign_pub hp h hx hy x21 x22 y21 y22
          xs ys
        have hc := core_ct v hp _ _ _ _ _ _ px py hp' eu ew
        exact ⟨by rw [hmeta, hc], trivial⟩
  intro x y tx ty x' y' hx hy hpub ex ey
  exact (trace _ _ _ _ _ _ ⟨hx, hy, hpub⟩ ex ey).1

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

def sharedSignSatWith (p : Params) (m : Mem) : State :=
  { pairedSignSatWith p m with
    rd := (signSat p).rd ++ [⟨0, 0⟩] ++ (pairedSignSatWith p m).rd.drop 3 }

theorem sharedSignSatWith_pre (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀ j < 488, m.readW (1048576 + BitVec.ofNat 64 (8 * j)) 64 =
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀ j < 488, m.readW (1052480 + BitVec.ofNat 64 (8 * j)) 64 =
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0)
    (hr : ∀ j < 512, m.readW (1056384 + BitVec.ofNat 64 (8 * j)) 64 =
      Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD j 0) :
    (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre (sharedSignSatWith p m) := by
  have old := pairedSignSatWith_pre p hp m hf hi hr
  have held : Abi.constsHeld m (fun name =>
      if name = "VG_MLDSA_NTT_EXPANDED" then 1048576 else
      if name = "VG_MLDSA_INV_FOLDED" then 1052480 else 1056384) pairedSignRootConsts := old.1.2.2.1
  have regions : Abi.constRegions (fun name =>
      if name = "VG_MLDSA_NTT_EXPANDED" then 1048576 else
      if name = "VG_MLDSA_INV_FOLDED" then 1052480 else 1056384) pairedSignRootConsts =
      [⟨1048576, 3904⟩, ⟨1052480, 3904⟩, ⟨1056384, 4096⟩] := by
    rw [pairedSignRootConsts_eq]
    simp only [Abi.constRegions, List.map_cons, List.map_nil,
      TableConstants.staticNttWords_length, InverseTable.expandedWords_length,
      PairedTable.expandedWords_length]
    rfl
  rcases hp with rfl | rfl | rfl
  all_goals
    apply Sig.contract_pre_of_check (sig := signWithCacheSig _)
      (A := abi.withConsts pairedSignRootConsts) (writeArgs := true) (stack := 48)
    · simp only [Sig.check, sharedSignSatWith, pairedSignSatWith, signSat,
        pairedSignRootConsts_eq, Abi.withConsts, abi, signWithCacheSig, signSig]
      simp only [Sig.words, Param.words, ArgWord.bits, IntTy.bits,
        List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.length_cons, List.length_nil]
      simp only [VG.AArch64.argRegs, List.length_cons, List.length_nil,
        Nat.reduceAdd, show (7 : Nat) ≤ 8 by decide, ↓reduceIte]
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil]
      dsimp only [Sig.bufs, Sig.lists, Sig.u64Bufs, Elem.size]
      rfl
    · change (48 ≤ (524288#64).toNat ∧ _ ∧ _ ∧ _ ∧ _) ∧ _
      refine ⟨⟨by decide, ?_, held, ?_, ?_⟩, Or.inl rfl⟩
      all_goals
        simp only [sharedSignSatWith, pairedSignSatWith, signSat, abi, regions, stackBelow, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        sig_and_intros
        all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide +kernel

theorem sharedSign_sat {p : Params} (hp : Ok3 p) :
    ∃ s, (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre s := by
  have old := pairedRoots_entry (by decide) (pairedSign_sat hp)
  exact ⟨sharedSignSatWith p (pairedSignSat p).mem,
    sharedSignSatWith_pre p hp _ old.2.1.forward.held old.2.1.inverse.held old.2.2.held⟩

theorem withCache_verified (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) (hp : Ok3 p) :
    Verified AArch64.target
      (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p)
      (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48) :=
  ⟨withCache_correct v hp, withCache_ct v hp, sharedSign_sat hp⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Verify

def verifyingMetadata (s : State) : State :=
  (s.write .x .x21 (s.gpr .x4)).write .x .x22 (s.gpr .x5)

theorem publicCache_metadata {p : Params} {S : Nat} {s : State} (hp : Sign.Ok3 p)
    (hlen : (s.gpr .x5).toNat = 1024 * p.k)
    (hr : Covers [⟨s.gpr .x4, (s.gpr .x5).toNat⟩] (s.rd ++ s.wr))
    (hw : ∀ R ∈ s.wr, (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint R)
    (hs : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint (below s.sp S))
    (hv : CachedPublicPolys p s.mem (s.gpr .x4) (vPk p s)) :
    PublicCache p S s (verifyingMetadata s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hp with rfl | rfl | rfl <;> decide
  · simpa [verifyingMetadata, State.write, hlen] using hr
  · simpa [verifyingMetadata, State.write, hlen] using hw
  · simpa [verifyingMetadata, State.write, hlen] using hs
  · intro i hi
    have hpoly := hv i hi
    rw [VG.Proof.MlDsa.PreparedKey.public_poly p (vPk p s) hi] at hpoly
    simpa [verifyingMetadata, State.write, pa, n] using hpoly

theorem shared_verify_scalar_input {p : Params} (hp : Sign.Ok3 p) {s : State}
    (h : (verifyWithCacheContract p abi 48).pre s) :
    vPre p 48 s ∧ (s.gpr .x5 ≠ 0 → PublicCache p 48 s (verifyingMetadata s)) := by
  sig_pre [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs] at h
  obtain ⟨hsp, hrd, hwr, d1, d2, d3, dc, k1, k2, k3, k4, kc, n1, n2, n3, n4, _nc, hcache⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · sig_pre [verifyContract, verifySig, abi, VG.AArch64.argRegs]
    exact ⟨hsp, rfl, hwr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, n4⟩
  · intro R hR
    rw [hrd]
    simp only [vInputs, List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with rfl | rfl | rfl <;> simp
  · intro hn
    rcases hcache with hz | ⟨hlen, hv⟩
    · exact absurd hz hn
    change (s.gpr .x5).toNat = 1024 * p.k at hlen
    apply publicCache_metadata hp hlen ?_ ?_ kc.symm hv
    · apply Covers.one
      exact ⟨⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
        List.mem_append_left _ (by rw [hrd]; simp), Region.contains_self _ _⟩
    · intro R hR
      rw [hwr] at hR
      obtain rfl := List.mem_singleton.mp hR
      exact dc.symm

theorem shared_verify_optimized_input {p : Params} (hp : Sign.Ok3 p) {s : State}
    (h : (verifyWithCacheContract p (abi.withConsts Sign.signRootConsts) 48).pre s) :
    vPre p 48 s ∧ Sign.StaticRoots 48 s ∧
      (s.gpr .x5 ≠ 0 → PublicCache p 48 s (verifyingMetadata s)) := by
  sig_pre [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs,
    Abi.withConsts, Sign.signRootConsts_eq, Abi.constRegions, Abi.constsHeld,
    VG.Proof.MlDsa.AArch64.Optimized.TableConstants.staticNttWords_length,
    VG.Proof.MlDsa.AArch64.Optimized.InverseTable.expandedWords_length, stackBelow] at h
  obtain ⟨hsp, hd, hf, hi, hff, hfw, hfs, hif, hiw, his, hfa, hia, ht, hwr,
    d1, d2, d3, dc, k1, k2, k3, k4, kc, n1, n2, n3, n4, _nc, hcache⟩ := h
  have hrd : s.rd = [⟨s.gpr .x0, p.pkLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, p.sigLen⟩,
      ⟨s.gpr .x4, (s.gpr .x5).toNat⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED", 3904⟩, ⟨s.syms "VG_MLDSA_INV_FOLDED", 3904⟩] := by
    rw [← List.take_append_drop (s.rd.length - 2) s.rd, ht, hd]
  refine ⟨⟨?_, ?_⟩, ⟨⟨hf, hff, ?_, hfw, hfs, hfa⟩, ⟨hi, hif, ?_, hiw, his, hia⟩⟩, ?_⟩
  · sig_pre [verifyContract, verifySig, abi, VG.AArch64.argRegs]
    exact ⟨hsp, rfl, hwr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, n4⟩
  · intro R hR
    rw [hrd]
    simp only [vInputs, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> simp
  · apply Covers.one
    exact ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED", 3904⟩,
      List.mem_append_left _ (by rw [hrd]; simp), Region.contains_self _ _⟩
  · apply Covers.one
    exact ⟨⟨s.syms "VG_MLDSA_INV_FOLDED", 3904⟩,
      List.mem_append_left _ (by rw [hrd]; simp), Region.contains_self _ _⟩
  · intro hn
    rcases hcache with hz | ⟨hlen, hv⟩
    · exact absurd hz hn
    change (s.gpr .x5).toNat = 1024 * p.k at hlen
    apply publicCache_metadata hp hlen ?_ ?_ kc.symm hv
    · apply Covers.one
      exact ⟨⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
        List.mem_append_left _ (by rw [hrd]; simp), Region.contains_self _ _⟩
    · intro R hR
      rw [hwr] at hR
      obtain rfl := List.mem_singleton.mp hR
      exact dc.symm

theorem shared_verify_input (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    {s : State} (h : (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pre s) :
    vPre p 48 s ∧ (v.callee.pairedSha3 = true → Sign.StaticRoots 48 s) ∧
      (s.gpr .x5 ≠ 0 → PublicCache p 48 s (verifyingMetadata s)) := by
  by_cases hpair : v.callee.pairedSha3 = true
  · have pre : (verifyWithCacheContract p (abi.withConsts Sign.signRootConsts) 48).pre s := by
      simpa only [Verify.OptimizedSelected.selectedAbi, Verify.OptimizedSelected.selectedConsts, hpair, ↓reduceIte] using h
    obtain ⟨hp', roots, cache⟩ := shared_verify_optimized_input hp pre
    exact ⟨hp', fun _ => roots, cache⟩
  · have hfalse : v.callee.pairedSha3 = false := Bool.eq_false_iff.mpr hpair
    have pre : (verifyWithCacheContract p abi 48).pre s := by
      simpa only [Verify.OptimizedSelected.selectedAbi, Verify.OptimizedSelected.selectedConsts, hfalse,
        Bool.false_eq_true, ↓reduceIte, show abi.withConsts [] = abi by rfl] using h
    obtain ⟨hp', cache⟩ := shared_verify_scalar_input hp pre
    exact ⟨hp', fun ht => absurd ht hpair, cache⟩

theorem verify_metadata_setup (s : State) :
    WP isa (.block [.addImm .x .x21 .x4 0, .addImm .x .x22 .x5 0]) s fun t =>
      VG.Proof.MlKem.AArch64.Only [.x21, .x22] s t ∧
      t.gpr .x21 = s.gpr .x4 ∧ t.gpr .x22 = s.gpr .x5 := by
  open VG.Proof.MlKem.AArch64 in
  refine wp_addImm (by decide) fun u hu h21 => wp_addImm (by decide) fun t ht h22 => wp_nil ?_
  exact ⟨(hu.trans ht).mono (by simp), by rw [ht.get .x21, h21, BitVec.add_zero],
    by rw [h22, BitVec.add_zero, hu.get .x5]⟩

theorem setup_verify_inputs (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    {σ s : State} (hpre : (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pre σ)
    (hs : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signInner σ) s)
    (h21 : s.gpr .x21 = σ.gpr .x4) (h22 : s.gpr .x22 = σ.gpr .x5) (hy : s.syms = σ.syms) :
    (verifyCoreK p v.callee.pairedSha3).pre s ∧ vPk p s = vPk p σ ∧
      vMu s = vMu σ ∧ vSig p s = vSig p σ := by
  obtain ⟨pre, roots, cached⟩ := shared_verify_input v hp hpre
  have e0 : s.gpr .x0 = σ.gpr .x0 := hs.get .x0
  have e1 : s.gpr .x1 = σ.gpr .x1 := hs.get .x1
  have e2 : s.gpr .x2 = σ.gpr .x2 := hs.get .x2
  have e3 : s.gpr .x3 = σ.gpr .x3 := hs.get .x3
  have er : s.rd = σ.rd := hs.rd
  have ew : s.wr = σ.wr := hs.wr
  have esp : s.sp = σ.sp - 32 := hs.sp.trans (signInner_sp σ)
  have hframe : Frame [below σ.sp 32] σ.mem s.mem := by rw [hs.mem]; exact signInner_frame σ
  have hsmall : Region.Sub (below σ.sp 32) (below σ.sp 48) := below_sub (by decide) (by decide)
  have hstack : Region.Sub (below s.sp 16) (below σ.sp 48) := by
    rw [esp]
    exact below_below σ.sp 32 16
  have p0 := pre.1
  sig_pre [verifyContract, verifySig, abi, VG.AArch64.argRegs] at p0
  obtain ⟨hsp, _, hwr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, n4⟩ := p0
  have hpk : vPk p s = vPk p σ := by
    rw [vPk, vPk, e0]
    exact MlKem.bytesAt_frame hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact (k1.sub_left hsmall).symm) (by rcases hp with rfl | rfl | rfl <;> decide)
  have hmu : vMu s = vMu σ := by
    rw [vMu, vMu, e1]
    exact MlKem.bytesAt_frame hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact (k2.sub_left hsmall).symm) (by decide)
  have hsig : vSig p s = vSig p σ := by
    rw [vSig, vSig, e2]
    exact MlKem.bytesAt_frame hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact (k3.sub_left hsmall).symm) (by rcases hp with rfl | rfl | rfl <;> decide)
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hpk, hmu, hsig⟩
  · sig_pre [verifyContract, verifySig, abi, VG.AArch64.argRegs]
    rw [ew, e0, e1, e2, e3]
    refine ⟨?_, (by simp only [vInputs, e0, e1, e2]), hwr, d1, d2, d3, k1.sub_left hstack, k2.sub_left hstack,
      k3.sub_left hstack, k4.sub_left hstack, n1, n2, n3, n4⟩
    rw [esp]
    change 16 ≤ (σ.sp - BitVec.ofNat 64 32).toNat
    rw [toNat_sub_ofNat' (by omega)]
    omega
  · intro R hR
    rw [er]
    apply pre.2 R
    simpa only [vInputs, e0, e1, e2] using hR
  · intro hpair
    have hr := roots hpair
    exact ⟨staticTable_reframe hr.forward hframe (fun R hR => by
        obtain rfl := List.mem_singleton.mp hR
        exact hr.forward.stack.sub_right hsmall) er ew hy hstack,
      staticTable_reframe hr.inverse hframe (fun R hR => by
        obtain rfl := List.mem_singleton.mp hR
        exact hr.inverse.stack.sub_right hsmall) er ew hy hstack⟩
  · intro hn
    have hc := cached (show σ.gpr .x5 ≠ 0 by rwa [h22] at hn)
    have e21 : s.gpr .x21 = (verifyingMetadata σ).gpr .x21 := by
      simpa [verifyingMetadata, State.write] using h21
    have hc' : PublicCache p 16 σ s := cache_reframe hc hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact hc.stack.sub_right hsmall) e21 er ew hstack
    change ReadCache p.k 16 (fun r => VG.Proof.MlDsa.Verify.t1Hat (vPk p s) r) s
    rw [hpk]
    exact hc'

theorem verify_frame_guards {p : Params} {σ s : State} (pre : vPre p 48 σ)
    {offset : Nat} (ho : offset ≤ 32) (hw : s.wr = σ.wr)
    (hsp : s.sp = σ.sp - BitVec.ofNat 64 offset) :
    16 ≤ s.sp.toNat ∧ ∀ R ∈ s.wr, Region.Disjoint ⟨s.sp - 16, 16⟩ R := by
  have hp := pre.1
  sig_pre [verifyContract, verifySig, abi, VG.AArch64.argRegs] at hp
  obtain ⟨hstack, _, hwr, _, _, _, _, _, _, k4, _, _, _, _⟩ := hp
  have hsub : Region.Sub (⟨s.sp - 16, 16⟩ : Region) (below σ.sp 48) := by
    have h1 := below_below σ.sp offset 16
    have h2 := below_sub (sp := σ.sp) (a := 16 + offset) (b := 48) (by omega) (by decide)
    rw [hsp]
    exact fun a ha => h2 a (h1 a ha)
  refine ⟨?_, ?_⟩
  · rw [hsp, toNat_sub_ofNat' (by omega)]
    omega
  · intro R hR
    rw [hw, hwr] at hR
    obtain rfl := List.mem_singleton.mp hR
    exact k4.sub_left hsub

theorem verify_withCache_correct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    (σ : State) (hpre : (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pre σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
      (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) σ tr t ∧ abiPreserved σ t ∧
      (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).post σ t := by
  have pre := (shared_verify_input v hp hpre).1
  have hd := common_frame_bounds (verify_core_dle v p).le
  have g0 := verify_frame_guards (s := σ) pre (offset := 0) (by decide) rfl (by simp)
  have g1 := verify_frame_guards (s := pushState .x21 σ) pre (offset := 16) (by decide) rfl rfl
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
      (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) σ
      fun t => abiPreserved σ t ∧ (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).post σ t := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.withCache
    refine WP.frameReg g0.1 g0.2 ?_ (by
      simpa only [Code.aarch64Depth, Instr.frameUnits, Nat.zero_max] using hd.1)
    refine WP.frameReg g1.1 g1.2 ?_ (by
      simpa only [Code.aarch64Depth, Nat.zero_max] using hd.2)
    refine WP.seq (WP.mono_syms (verify_metadata_setup (signInner σ)) fun s ⟨hs, h21, h22⟩ hy => ?_)
    obtain ⟨hcore, hpk, hmu, hsig⟩ := setup_verify_inputs v hp hpre hs h21 h22 hy
    obtain ⟨tr, t, he, habi, hpost⟩ := verify_core_correct v hp s hcore
    refine ⟨tr, t, he, ⟨?_, rfl, ?_⟩, ?_⟩
    · intro r hr
      by_cases e21 : r = .x21
      · subst r; simp [State.write]
      by_cases e22 : r = .x22
      · subst r; simp [State.write]
      simp only [State.write, e21, e22, ite_false]
      rw [habi.1 r hr, hs.get r (by simp [e21, e22])]
      rfl
    · intro r hr
      exact (habi.2.2 r hr).trans (hs.vcs r hr)
    · change ((t.gpr .x0).setWidth 32 = 1 ∧ ∃ b, verifyMu p b (vPk p s) (vMu s) (vSig p s) = some true) ∨
        ((t.gpr .x0).setWidth 32 = 0 ∧ verifyMu p minBounds (vPk p s) (vMu s) (vSig p s) ≠ some true) at hpost
      rw [hpk, hmu, hsig] at hpost
      by_cases hpair : v.callee.pairedSha3 = true
      · have hab : Verify.OptimizedSelected.selectedAbi v = abi.withConsts Sign.signRootConsts := by
          simp only [Verify.OptimizedSelected.selectedAbi, Verify.OptimizedSelected.selectedConsts, hpair, ↓reduceIte]
        rw [hab]
        sig_post [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs,
          Abi.withConsts, Sign.signRootConsts_eq]
        simpa [vPk, vMu, vSig, State.write] using hpost
      · have hfalse : v.callee.pairedSha3 = false := Bool.eq_false_iff.mpr hpair
        have hab : Verify.OptimizedSelected.selectedAbi v = abi := by
          simp only [Verify.OptimizedSelected.selectedAbi, Verify.OptimizedSelected.selectedConsts, hfalse,
            Bool.false_eq_true, ↓reduceIte, show abi.withConsts [] = abi by rfl]
        rw [hab]
        sig_post [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs]
        simpa [vPk, vMu, vSig, State.write] using hpost
  obtain ⟨tr, t, he, habi, hpost⟩ := main
  exact ⟨tr, t, he, habi, hpost⟩

theorem shared_verify_pub (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} {x y : State}
    (h : (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pub x y) :
    vPub p 48 x y ∧ (x.gpr .x4 = y.gpr .x4 ∧ x.gpr .x5 = y.gpr .x5) ∧
      (v.callee.pairedSha3 = true → Sign.RootSymbolsEq x y) := by
  by_cases hpair : v.callee.pairedSha3 = true
  · have hab : Verify.OptimizedSelected.selectedAbi v = abi.withConsts Sign.signRootConsts := by
      simp only [Verify.OptimizedSelected.selectedAbi, Verify.OptimizedSelected.selectedConsts, hpair, ↓reduceIte]
    rw [hab] at h
    sig_pub [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs,
      Abi.withConsts, Sign.signRootConsts_eq] at h
    obtain ⟨hsp, hf, hi, hb, h0, h1, h2, h3, h4, h5⟩ := h
    refine ⟨?_, ⟨h4, h5⟩, fun _ => ⟨hf, hi⟩⟩
    sig_pub [vPub, verifyContract, verifySig, abi, VG.AArch64.argRegs]
    exact ⟨hsp, hb, h0, h1, h2, h3⟩
  · have hfalse : v.callee.pairedSha3 = false := Bool.eq_false_iff.mpr hpair
    have hab : Verify.OptimizedSelected.selectedAbi v = abi := by
      simp only [Verify.OptimizedSelected.selectedAbi, Verify.OptimizedSelected.selectedConsts, hfalse,
        Bool.false_eq_true, ↓reduceIte, show abi.withConsts [] = abi by rfl]
    rw [hab] at h
    sig_pub [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs] at h
    obtain ⟨hsp, hb, h0, h1, h2, h3, h4, h5⟩ := h
    refine ⟨?_, ⟨h4, h5⟩, fun ht => absurd ht hpair⟩
    sig_pub [vPub, verifyContract, verifySig, abi, VG.AArch64.argRegs]
    exact ⟨hsp, hb, h0, h1, h2, h3⟩

def SharedVerifyRel (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) (x y : State) : Prop :=
  (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pre x ∧
  (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pre y ∧
  (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pub x y

theorem setup_verify_pub (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    {σ τ x y : State} (h : SharedVerifyRel v p σ τ)
    (hx : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signPushed σ) x)
    (hy : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signPushed τ) y)
    (x21 : x.gpr .x21 = σ.gpr .x4) (x22 : x.gpr .x22 = σ.gpr .x5)
    (y21 : y.gpr .x21 = τ.gpr .x4) (y22 : y.gpr .x22 = τ.gpr .x5)
    (xs : x.syms = σ.syms) (ys : y.syms = τ.syms) :
    (verifyCoreK p v.callee.pairedSha3).pub (x.withRegions σ.rd σ.wr) (y.withRegions τ.rd τ.wr) := by
  have nx := setup_verify_inputs v hp h.1 (sign_setup_narrow hx) x21 x22 xs
  have ny := setup_verify_inputs v hp h.2.1 (sign_setup_narrow hy) y21 y22 ys
  obtain ⟨pub, ⟨h4, h5⟩, roots⟩ := shared_verify_pub v h.2.2
  obtain ⟨hsp, hpk, hmu, hsig, h0, h1, h2, h3⟩ := vPub_eq pub
  have esp : x.sp = y.sp := by
    rw [hx.sp, hy.sp]
    change (σ.sp - 16) - 16 = (τ.sp - 16) - 16
    rw [hsp]
  refine ⟨?_, ?_, ?_⟩
  · sig_pub [vPub, verifyContract, verifySig, abi, VG.AArch64.argRegs]
    refine ⟨esp, ?_, ?_, ?_, ?_, ?_⟩
    · change leakBytes (vPk p _ ++ vMu _ ++ vSig p _) = leakBytes (vPk p _ ++ vMu _ ++ vSig p _)
      have xpk : vPk p x = vPk p σ := nx.2.1
      have xmu : vMu x = vMu σ := nx.2.2.1
      have xsig : vSig p x = vSig p σ := nx.2.2.2
      have ypk : vPk p y = vPk p τ := ny.2.1
      have ymu : vMu y = vMu τ := ny.2.2.1
      have ysig : vSig p y = vSig p τ := ny.2.2.2
      rw [xpk, xmu, xsig, ypk, ymu, ysig, hpk, hmu, hsig]
    · exact (hx.get .x0).trans (h0.trans (hy.get .x0).symm)
    · exact (hx.get .x1).trans (h1.trans (hy.get .x1).symm)
    · exact (hx.get .x2).trans (h2.trans (hy.get .x2).symm)
    · exact (hx.get .x3).trans (h3.trans (hy.get .x3).symm)
  · intro hpair
    simpa only [Sign.RootSymbolsEq, State.withRegions, xs, ys] using roots hpair
  · refine ⟨fun r hr => ?_, esp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact x21.trans (h4.trans y21.symm)
    · exact x22.trans (h5.trans y22.symm)

theorem verify_withCache_ct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p) :
    ConstantTime isa (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pre
      (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pub
      (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  have hs : ∀ x y, SharedVerifyRel v p x y → x.sp = y.sp := by
    intro x y h
    exact (vPub_eq (shared_verify_pub v h.2.2).1).1
  have trace : RelCT isa (SharedVerifyRel v p)
      (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p)
      (fun _ _ => True) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.withCache
    refine frame_tr hs (frame_tr (pushRel_sp hs) (R := fun _ _ => True) ?_)
    intro a b ta tb a' b' h ex ey
    rcases h with ⟨a1, b1, ⟨σ, τ, h, rfl, rfl⟩, rfl, rfl⟩
    cases ex with
    | seq ax bx =>
      cases ey with
      | seq ay by' =>
        have pub := shared_verify_pub v h.2.2
        have hsp := (vPub_eq pub.1).1
        have h5 := pub.2.1.1
        have h6 := pub.2.1.2
        have ht : RelCT isa (fun x y => AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x4, .x5]) x y)
            (.block [.addImm .x .x21 .x4 0, .addImm .x .x22 .x5 0]) (fun _ _ => True) :=
          taintRel [.x4, .x5] (fun _ _ h => ⟨h.1, fun r hr => h.2 r (AArch64.Taint.mem_ofRegs.mpr hr)⟩) (by taint_decide)
        have agree : AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x4, .x5])
            (signPushed σ) (signPushed τ) := by
          refine ⟨?_, fun r hr => ?_⟩
          · change (σ.sp - 16) - 16 = (τ.sp - 16) - 16
            rw [hsp]
          · simp only [AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            exacts [h5, h6]
        have hmeta := (ht _ _ _ _ _ _ agree ax ay).1
        obtain ⟨_, x, exx, hx, x21, x22⟩ := verify_metadata_setup (signPushed σ)
        obtain ⟨_, y, eyy, hy, y21, y22⟩ := verify_metadata_setup (signPushed τ)
        have exeq := (Exec.det ax exx).2
        have eyeq := (Exec.det ay eyy).2
        rw [exeq] at ax bx
        rw [eyeq] at ay by'
        have xs0 := VG.AArch64.Exec.syms ax
        have xs : x.syms = σ.syms := xs0
        have ys0 := VG.AArch64.Exec.syms ay
        have ys : y.syms = τ.syms := ys0
        have nx := setup_verify_inputs v hp h.1 (sign_setup_narrow hx) x21 x22 xs
        have ny := setup_verify_inputs v hp h.2.1 (sign_setup_narrow hy) y21 y22 ys
        have rx : Covers (σ.rd ++ σ.wr) (x.rd ++ x.wr) := by
          rw [hx.rd, hx.wr]
          exact Covers.append (Covers.refl _) (signPushed_wr_cover σ)
        have ry : Covers (τ.rd ++ τ.wr) (y.rd ++ y.wr) := by
          rw [hy.rd, hy.wr]
          exact Covers.append (Covers.refl _) (signPushed_wr_cover τ)
        have wx : Covers σ.wr x.wr := by rw [hx.wr]; exact signPushed_wr_cover σ
        have wy : Covers τ.wr y.wr := by rw [hy.wr]; exact signPushed_wr_cover τ
        have px : (verifyCoreK p v.callee.pairedSha3).pre (x.withRegions σ.rd σ.wr) := nx.1
        have py : (verifyCoreK p v.callee.pairedSha3).pre (y.withRegions τ.rd τ.wr) := ny.1
        obtain ⟨u, eu⟩ := trace_narrow (verify_core_correct v hp) px rx wx bx
        obtain ⟨w, ew⟩ := trace_narrow (verify_core_correct v hp) py ry wy by'
        have hp' := setup_verify_pub v hp h hx hy x21 x22 y21 y22
          xs ys
        have hc := verify_core_ct v hp _ _ _ _ _ _ px py hp' eu ew
        exact ⟨by rw [hmeta, hc], trivial⟩
  intro x y tx ty x' y' hx hy hpub ex ey
  exact (trace _ _ _ _ _ _ ⟨hx, hy, hpub⟩ ex ey).1


def sharedVerifyScalarSat (p : Params) : State :=
  { Verify.Optimized.baseSat p with rd := (Verify.Optimized.baseSat p).rd ++ [⟨0, 0⟩] }

theorem sharedVerifyScalar_sat {p : Params} (hp : Sign.Ok3 p) :
    (verifyWithCacheContract p abi 48).pre (sharedVerifyScalarSat p) := by
  rcases hp with rfl | rfl | rfl
  all_goals
    sig_apply_check
    · decide +kernel
    · sig_reduce [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs,
        sharedVerifyScalarSat, Verify.Optimized.baseSat]
      exact ⟨by decide, Or.inl rfl⟩

def sharedVerifySatWith (p : Params) (m : Mem) : State :=
  { Verify.Optimized.verifySatWith p m with
    rd := (Verify.Optimized.baseSat p).rd ++ [⟨0, 0⟩] ++ (Verify.Optimized.verifySatWith p m).rd.drop 3 }

theorem sharedVerifySatWith_pre (p : Params) (hp : Sign.Ok3 p) (m : Mem)
    (hf : ∀ j < 488, m.readW (1048576 + BitVec.ofNat 64 (8 * j)) 64 =
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀ j < 488, m.readW (1052480 + BitVec.ofNat 64 (8 * j)) 64 =
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0) :
    (verifyWithCacheContract p (abi.withConsts Sign.signRootConsts) 48).pre (sharedVerifySatWith p m) := by
  have old := Verify.Optimized.verifySatWith_pre p hp m hf hi
  have held : Abi.constsHeld m (fun name =>
      if name = "VG_MLDSA_NTT_EXPANDED" then 1048576 else 1052480) Sign.signRootConsts := old.1.2.2.1
  have regions : Abi.constRegions (fun name =>
      if name = "VG_MLDSA_NTT_EXPANDED" then 1048576 else 1052480) Sign.signRootConsts =
      [⟨1048576, 3904⟩, ⟨1052480, 3904⟩] := by
    rw [Sign.signRootConsts_eq]
    simp only [Abi.constRegions, List.map_cons, List.map_nil,
      VG.Proof.MlDsa.AArch64.Optimized.TableConstants.staticNttWords_length, VG.Proof.MlDsa.AArch64.Optimized.InverseTable.expandedWords_length]
    rfl
  rcases hp with rfl | rfl | rfl
  all_goals
    apply Sig.contract_pre_of_check (sig := verifyWithCacheSig _)
      (A := abi.withConsts Sign.signRootConsts) (writeArgs := true) (stack := 48)
    · simp only [Sig.check, sharedVerifySatWith, Verify.Optimized.verifySatWith, Verify.Optimized.baseSat,
        Sign.signRootConsts_eq, Abi.withConsts, abi, verifyWithCacheSig, verifySig]
      simp only [Sig.words, Param.words, ArgWord.bits, IntTy.bits,
        List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.length_cons, List.length_nil]
      simp only [VG.AArch64.argRegs, List.length_cons, List.length_nil,
        Nat.reduceAdd, show (6 : Nat) ≤ 8 by decide, ↓reduceIte]
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil]
      dsimp only [Sig.bufs, Sig.lists, Sig.u64Bufs, Elem.size]
      rfl
    · change (48 ≤ (524288#64).toNat ∧ _ ∧ _ ∧ _ ∧ _) ∧ _
      refine ⟨⟨by decide, ?_, held, ?_, ?_⟩, Or.inl rfl⟩
      all_goals
        simp only [sharedVerifySatWith, Verify.Optimized.verifySatWith, Verify.Optimized.baseSat,
          abi, regions, stackBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        sig_and_intros
        all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide +kernel

theorem shared_verify_sat (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p) :
    ∃ s, (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48).pre s := by
  by_cases hpair : v.callee.pairedSha3 = true
  · have hab : Verify.OptimizedSelected.selectedAbi v = abi.withConsts Sign.signRootConsts := by
      simp only [Verify.OptimizedSelected.selectedAbi, Verify.OptimizedSelected.selectedConsts, hpair, ↓reduceIte]
    rw [hab]
    have roots := (Sign.pairedRoots_entry (by decide) (Sign.pairedSign_sat hp)).2.1
    exact ⟨sharedVerifySatWith p (Sign.pairedSignSat p).mem,
      sharedVerifySatWith_pre p hp _ roots.forward.held roots.inverse.held⟩
  · have hfalse : v.callee.pairedSha3 = false := Bool.eq_false_iff.mpr hpair
    have hab : Verify.OptimizedSelected.selectedAbi v = abi := by
      simp only [Verify.OptimizedSelected.selectedAbi, Verify.OptimizedSelected.selectedConsts, hfalse,
        Bool.false_eq_true, ↓reduceIte, show abi.withConsts [] = abi by rfl]
    rw [hab]
    exact ⟨sharedVerifyScalarSat p, sharedVerifyScalar_sat hp⟩

theorem verify_withCache_verified (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) (hp : Sign.Ok3 p) :
    Verified AArch64.target (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
      (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p)
      (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi v) 48) :=
  ⟨verify_withCache_correct v hp, verify_withCache_ct v hp, shared_verify_sat v hp⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## Ordinary and prepared operation entry points -/

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Call (lea movV)

def operationSetup (p : Params) (sign prepared : Bool) : List Instr :=
  if sign then
    if prepared then lea .x5 .x0 p.skLen ++ movV .x6 (1024 * (p.ℓ + 2 * p.k))
    else [.addImm .x .x5 .x0 0] ++ movV .x6 0
  else
    if prepared then lea .x4 .x0 p.pkLen ++ movV .x5 (1024 * p.k)
    else [.addImm .x .x4 .x0 0] ++ movV .x5 0

theorem operationSetup_ok (p : Params) (sign prepared : Bool) (s : State) :
    WP isa (.block (operationSetup p sign prepared)) s fun t =>
      Only (if sign then [.x5, .x6] else [.x4, .x5]) s t ∧
      t.gpr (if sign then .x5 else .x4) = s.gpr .x0 +
        BitVec.ofNat 64 (if prepared then (if sign then p.skLen else p.pkLen) else 0) ∧
      t.gpr (if sign then .x6 else .x5) = BitVec.ofNat 64
        (if prepared then 1024 * (if sign then p.ℓ + 2 * p.k else p.k) else 0) := by
  cases sign <;> cases prepared
  all_goals simp only [operationSetup, Bool.false_eq_true, ↓reduceIte]
  · refine wp_addImm (by decide) fun u hu h4 => movV_ok .x5 0 fun t ht h5 => wp_nil ?_
    exact ⟨(hu.trans ht).mono (by simp), by rw [ht.get .x4, h4], h5⟩
  · refine lea_ok (by decide) p.pkLen fun u hu h4 => ?_
    rw [← List.append_nil (movV .x5 (1024 * p.k))]
    refine movV_ok .x5 (1024 * p.k) fun t ht h5 => wp_nil ?_
    exact ⟨(hu.trans ht).mono (by simp), by rw [ht.get .x4, h4], h5⟩
  · refine wp_addImm (by decide) fun u hu h5 => movV_ok .x6 0 fun t ht h6 => wp_nil ?_
    exact ⟨(hu.trans ht).mono (by simp), by rw [ht.get .x5, h5], h6⟩
  · refine lea_ok (by decide) p.skLen fun u hu h5 => ?_
    rw [← List.append_nil (movV .x6 (1024 * (p.ℓ + 2 * p.k)))]
    refine movV_ok .x6 (1024 * (p.ℓ + 2 * p.k)) fun t ht h6 => wp_nil ?_
    exact ⟨(hu.trans ht).mono (by simp), by rw [ht.get .x5, h5], h6⟩

theorem sign_withCache_dle (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params}
    (hp : Sign.Ok3 p) : Message.DLe 3
      (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (Sign.primsWith v.callee) p) := by
  have hd := (core_dle v hp).le
  exact ⟨by simpa only [Impl.MlDsa.AArch64.PreparedKey.Sign.withCache,
    Code.aarch64Depth, Nat.zero_max, Instr.frameUnits] using Nat.add_le_add_right hd 2⟩

theorem verify_withCache_dle (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) : Message.DLe 3
      (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
        (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  have hd := (verify_core_dle v p).le
  exact ⟨by simpa only [Impl.MlDsa.AArch64.PreparedKey.Verify.withCache,
    Code.aarch64Depth, Nat.zero_max, Instr.frameUnits] using Nat.add_le_add_right hd 2⟩

theorem prepared_public_cache_frame {p : Params} {m m' : Mem} {key : Addr} {W : List Region}
    (h : PreparedPublicKey p m key) (hf : Frame W m m')
    (hd : ∀ R ∈ W, (⟨key, preparedPublicKeyBytes p⟩ : Region).Disjoint R)
    (hb : preparedPublicKeyBytes p < 2 ^ 32) :
    CachedPublicPolys p m' (key + BitVec.ofNat 64 p.pkLen)
      (VG.Spec.Sha3.bytesAt m' key p.pkLen) := by
  have hs : Region.Sub (⟨key, p.pkLen⟩ : Region) ⟨key, preparedPublicKeyBytes p⟩ :=
    Region.sub_prefix (by simp only [preparedPublicKeyBytes]; omega)
  have hk := VG.Proof.MlKem.bytesAt_frame hf (fun R hR => (hd R hR).sub_left hs)
    (by simp only [preparedPublicKeyBytes] at hb; omega)
  intro i hi
  change PolyIs m' ((key + BitVec.ofNat 64 p.pkLen) + BitVec.ofNat 64 (4 * n * i)) _
  rw [VG.Offset.add_add, hk]
  exact VG.Proof.MlDsa.Verify.polyIs_frame hf (fun R hR => (hd R hR).sub_left
    (by
      change Region.Sub ⟨key + BitVec.ofNat 64 (p.pkLen + 4 * n * i), 1024⟩ _
      apply VG.Offset.sub_base key
      simp only [preparedPublicKeyBytes, n]
      omega)) (h i hi)

theorem prepared_secret_cache_frame {p : Params} {m m' : Mem} {key : Addr} {W : List Region}
    (h : PreparedSecretKey p m key) (hf : Frame W m m')
    (hd : ∀ R ∈ W, (⟨key, preparedSecretKeyBytes p⟩ : Region).Disjoint R)
    (hb : preparedSecretKeyBytes p < 2 ^ 32) :
    CachedSecretPolys p m' (key + BitVec.ofNat 64 p.skLen)
      (VG.Spec.Sha3.bytesAt m' key p.skLen) := by
  have hs : Region.Sub (⟨key, p.skLen⟩ : Region) ⟨key, preparedSecretKeyBytes p⟩ :=
    Region.sub_prefix (by simp only [preparedSecretKeyBytes]; omega)
  have hk := VG.Proof.MlKem.bytesAt_frame hf (fun R hR => (hd R hR).sub_left hs)
    (by simp only [preparedSecretKeyBytes] at hb; omega)
  intro i hi
  change PolyIs m' ((key + BitVec.ofNat 64 p.skLen) + BitVec.ofNat 64 (4 * n * i)) _
  rw [VG.Offset.add_add, hk]
  exact VG.Proof.MlDsa.Verify.polyIs_frame hf (fun R hR => (hd R hR).sub_left
    (by
      change Region.Sub ⟨key + BitVec.ofNat 64 (p.skLen + 4 * n * i), 1024⟩ _
      apply VG.Offset.sub_base key
      simp only [preparedSecretKeyBytes, n]
      omega)) (h i hi)

def verifyEntryRd (p : Params) (s : State) : List Region :=
  [⟨s.gpr .x0, p.pkLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, p.sigLen⟩,
    ⟨s.gpr .x4, (s.gpr .x5).toNat⟩]

theorem empty_disjoint (a : Addr) (r : Region) : (⟨a, 0⟩ : Region).Disjoint r := by
  intro x hx _
  simp only [Region.Contains] at hx
  omega

theorem verify_empty_pre {p : Params} {σ s : State}
    (pre : (verifyContract p abi 64).pre σ)
    (o : Only [.x4, .x5] (pushState .x30 σ) s)
    (h4 : s.gpr .x4 = σ.gpr .x0) (h5 : s.gpr .x5 = 0) :
    (verifyWithCacheContract p abi 48).pre
      (s.callEntry.withRegions (verifyEntryRd p s) σ.wr) := by
  sig_pre [verifyContract, verifySig, abi, VG.AArch64.argRegs] at pre
  obtain ⟨sp, rd, wr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, n4⟩ := pre
  have e0 : s.gpr .x0 = σ.gpr .x0 := o.get .x0 (by decide)
  have e1 : s.gpr .x1 = σ.gpr .x1 := o.get .x1 (by decide)
  have e2 : s.gpr .x2 = σ.gpr .x2 := o.get .x2 (by decide)
  have e3 : s.gpr .x3 = σ.gpr .x3 := o.get .x3 (by decide)
  have esp : s.sp = σ.sp - 16 := o.sp
  have ks : Region.Sub (below s.sp 48) (below σ.sp 64) := by
    rw [esp]
    exact below_below σ.sp 16 48
  have sn : 48 ≤ s.sp.toNat := by
    rw [esp]
    change 48 ≤ (σ.sp - BitVec.ofNat 64 16).toNat
    rw [toNat_sub_ofNat' (by omega)]
    omega
  sig_pre [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs]
  simp only [verifyEntryRd, h4, h5,
    e0, e1, e2, e3, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
  exact ⟨sn, True.intro, wr, d1, d2, d3, (empty_disjoint _ _).symm,
    k1.sub_left ks, k2.sub_left ks, k3.sub_left ks, k4.sub_left ks,
    (empty_disjoint _ _).symm, n1, n2, n3, n4,
    by have := (σ.gpr .x0).isLt; omega, Or.inl True.intro⟩

theorem verify_prepared_pre {p : Params} (hp : Sign.Ok3 p) {σ s : State}
    (pre : (preparedVerifyContract p abi 64).pre σ)
    (o : Only [.x4, .x5] (pushState .x30 σ) s)
    (h4 : s.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 p.pkLen)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (1024 * p.k)) :
    (verifyWithCacheContract p abi 48).pre
      (s.callEntry.withRegions (verifyEntryRd p s) σ.wr) := by
  sig_pre [preparedVerifyContract, preparedVerifySig, abi, VG.AArch64.argRegs] at pre
  obtain ⟨sp, rd, wr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, n4, cached⟩ := pre
  have hb : preparedPublicKeyBytes p < 2 ^ 32 := by
    rcases hp with rfl | rfl | rfl <;> decide
  have hn : n = 256 := rfl
  have small : 1024 * p.k < 2 ^ 64 := by rcases hp with rfl | rfl | rfl <;> decide
  have e0 : s.gpr .x0 = σ.gpr .x0 := o.get .x0 (by decide)
  have e1 : s.gpr .x1 = σ.gpr .x1 := o.get .x1 (by decide)
  have e2 : s.gpr .x2 = σ.gpr .x2 := o.get .x2 (by decide)
  have e3 : s.gpr .x3 = σ.gpr .x3 := o.get .x3 (by decide)
  have esp : s.sp = σ.sp - 16 := o.sp
  have ks : Region.Sub (below s.sp 48) (below σ.sp 64) := by
    rw [esp]
    exact below_below σ.sp 16 48
  have keyPrefix : Region.Sub (⟨σ.gpr .x0, p.pkLen⟩ : Region)
      ⟨σ.gpr .x0, preparedPublicKeyBytes p⟩ := Region.sub_prefix (by
    simp only [preparedPublicKeyBytes]; omega)
  have suffix : Region.Sub (⟨σ.gpr .x0 + BitVec.ofNat 64 p.pkLen, 1024 * p.k⟩ : Region)
      ⟨σ.gpr .x0, preparedPublicKeyBytes p⟩ := Offset.sub_base _ (by
    simp only [preparedPublicKeyBytes, hn]; omega)
  have sn : 48 ≤ s.sp.toNat := by
    rw [esp]
    change 48 ≤ (σ.sp - BitVec.ofNat 64 16).toNat
    rw [toNat_sub_ofNat' (by omega)]
    omega
  have cache : CachedPublicPolys p s.mem (σ.gpr .x0 + BitVec.ofNat 64 p.pkLen)
      (Spec.Sha3.bytesAt s.mem (σ.gpr .x0) p.pkLen) := by
    apply prepared_public_cache_frame cached (W := [below σ.sp 16]) ?_ ?_ hb
    · rw [o.mem]
      exact Frame.write (r := below σ.sp 16) (Frame.refl _ _) (by simp) _
        (by simp [Region.Contains])
    · intro R hR
      obtain rfl := List.mem_singleton.mp hR
      exact (k1.sub_left (below_sub (by decide) (by decide))).symm
  have nkey : (σ.gpr .x0).toNat + p.pkLen ≤ 2 ^ 64 := by
    simp only [preparedPublicKeyBytes] at n1
    omega
  have nsuffix : (σ.gpr .x0 + BitVec.ofNat 64 p.pkLen).toNat + 1024 * p.k ≤ 2 ^ 64 := by
    have bound : (σ.gpr .x0 + BitVec.ofNat 64 p.pkLen).toNat ≤
        (σ.gpr .x0).toNat + p.pkLen := by
      rw [Offset.toNat_add_ofNat]
      exact (Nat.mod_le _ _).trans (Nat.add_le_add_left (Nat.mod_le _ _) _)
    simp only [preparedPublicKeyBytes, hn] at n1
    omega
  sig_pre [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs]
  simp only [verifyEntryRd, h4, h5,
    e0, e1, e2, e3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  refine ⟨sn, True.intro, wr, d1.sub_left keyPrefix, d2, d3,
    (d1.sub_left suffix).symm, (k1.sub_left ks).sub_right keyPrefix,
    k2.sub_left ks, k3.sub_left ks, k4.sub_left ks,
    (k1.sub_left ks).sub_right suffix, nkey, n2, n3, n4, nsuffix, Or.inr ⟨?_, cache⟩⟩
  rw [hn]

def signEntryRd (p : Params) (s : State) : List Region :=
  [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩,
    ⟨s.gpr .x5, (s.gpr .x6).toNat⟩]

theorem sign_empty_pre {p : Params} {σ s : State}
    (pre : (signContract p abi 64).pre σ)
    (o : Only [.x5, .x6] (pushState .x30 σ) s)
    (h5 : s.gpr .x5 = σ.gpr .x0) (h6 : s.gpr .x6 = 0) :
    (signWithCacheContract p abi 48).pre
      (s.callEntry.withRegions (signEntryRd p s) σ.wr) := by
  sig_pre [signContract, signSig, abi, VG.AArch64.argRegs] at pre
  obtain ⟨sp, rd, wr, d1, d2, d3, d4, d5, d6, d7,
    k1, k2, k3, k4, k5, n1, n2, n3, n4, n5⟩ := pre
  have e0 : s.gpr .x0 = σ.gpr .x0 := o.get .x0 (by decide)
  have e1 : s.gpr .x1 = σ.gpr .x1 := o.get .x1 (by decide)
  have e2 : s.gpr .x2 = σ.gpr .x2 := o.get .x2 (by decide)
  have e3 : s.gpr .x3 = σ.gpr .x3 := o.get .x3 (by decide)
  have e4 : s.gpr .x4 = σ.gpr .x4 := o.get .x4 (by decide)
  have esp : s.sp = σ.sp - 16 := o.sp
  have ks : Region.Sub (below s.sp 48) (below σ.sp 64) := by
    rw [esp]
    exact below_below σ.sp 16 48
  have sn : 48 ≤ s.sp.toNat := by
    rw [esp]
    change 48 ≤ (σ.sp - BitVec.ofNat 64 16).toNat
    rw [toNat_sub_ofNat' (by omega)]
    omega
  sig_pre [signWithCacheContract, signWithCacheSig, signSig, abi, VG.AArch64.argRegs]
  simp only [signEntryRd, h5, h6, e0, e1, e2, e3, e4,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
  exact ⟨sn, True.intro, wr, d1, d2, d3, d4, d5, d6, d7,
    (empty_disjoint _ _).symm, (empty_disjoint _ _).symm,
    k1.sub_left ks, k2.sub_left ks, k3.sub_left ks, k4.sub_left ks, k5.sub_left ks,
    (empty_disjoint _ _).symm, n1, n2, n3, n4, n5,
    by have := (σ.gpr .x0).isLt; omega, Or.inl True.intro⟩

theorem sign_prepared_pre {p : Params} (hp : Sign.Ok3 p) {σ s : State}
    (pre : (preparedSignContract p abi 64).pre σ)
    (o : Only [.x5, .x6] (pushState .x30 σ) s)
    (h5 : s.gpr .x5 = σ.gpr .x0 + BitVec.ofNat 64 p.skLen)
    (h6 : s.gpr .x6 = BitVec.ofNat 64 (1024 * (p.ℓ + 2 * p.k))) :
    (signWithCacheContract p abi 48).pre
      (s.callEntry.withRegions (signEntryRd p s) σ.wr) := by
  sig_pre [preparedSignContract, preparedSignSig, abi, VG.AArch64.argRegs] at pre
  obtain ⟨sp, rd, wr, d1, d2, d3, d4, d5, d6, d7,
    k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, cached⟩ := pre
  have hb : preparedSecretKeyBytes p < 2 ^ 32 := by
    rcases hp with rfl | rfl | rfl <;> decide
  have hn : n = 256 := rfl
  have small : 1024 * (p.ℓ + 2 * p.k) < 2 ^ 64 := by rcases hp with rfl | rfl | rfl <;> decide
  have e0 : s.gpr .x0 = σ.gpr .x0 := o.get .x0 (by decide)
  have e1 : s.gpr .x1 = σ.gpr .x1 := o.get .x1 (by decide)
  have e2 : s.gpr .x2 = σ.gpr .x2 := o.get .x2 (by decide)
  have e3 : s.gpr .x3 = σ.gpr .x3 := o.get .x3 (by decide)
  have e4 : s.gpr .x4 = σ.gpr .x4 := o.get .x4 (by decide)
  have esp : s.sp = σ.sp - 16 := o.sp
  have ks : Region.Sub (below s.sp 48) (below σ.sp 64) := by
    rw [esp]
    exact below_below σ.sp 16 48
  have keyPrefix : Region.Sub (⟨σ.gpr .x0, p.skLen⟩ : Region)
      ⟨σ.gpr .x0, preparedSecretKeyBytes p⟩ := Region.sub_prefix (by
    simp only [preparedSecretKeyBytes]; omega)
  have suffix : Region.Sub (⟨σ.gpr .x0 + BitVec.ofNat 64 p.skLen, 1024 * (p.ℓ + 2 * p.k)⟩ : Region)
      ⟨σ.gpr .x0, preparedSecretKeyBytes p⟩ := Offset.sub_base _ (by
    simp only [preparedSecretKeyBytes, hn]; omega)
  have sn : 48 ≤ s.sp.toNat := by
    rw [esp]
    change 48 ≤ (σ.sp - BitVec.ofNat 64 16).toNat
    rw [toNat_sub_ofNat' (by omega)]
    omega
  have cache : CachedSecretPolys p s.mem (σ.gpr .x0 + BitVec.ofNat 64 p.skLen)
      (Spec.Sha3.bytesAt s.mem (σ.gpr .x0) p.skLen) := by
    apply prepared_secret_cache_frame cached (W := [below σ.sp 16]) ?_ ?_ hb
    · rw [o.mem]
      exact Frame.write (r := below σ.sp 16) (Frame.refl _ _) (by simp) _
        (by simp [Region.Contains])
    · intro R hR
      obtain rfl := List.mem_singleton.mp hR
      exact (k1.sub_left (below_sub (by decide) (by decide))).symm
  have nkey : (σ.gpr .x0).toNat + p.skLen ≤ 2 ^ 64 := by
    simp only [preparedSecretKeyBytes] at n1
    omega
  have nsuffix : (σ.gpr .x0 + BitVec.ofNat 64 p.skLen).toNat + 1024 * (p.ℓ + 2 * p.k) ≤ 2 ^ 64 := by
    have bound : (σ.gpr .x0 + BitVec.ofNat 64 p.skLen).toNat ≤
        (σ.gpr .x0).toNat + p.skLen := by
      rw [Offset.toNat_add_ofNat]
      exact (Nat.mod_le _ _).trans (Nat.add_le_add_left (Nat.mod_le _ _) _)
    simp only [preparedSecretKeyBytes, hn] at n1
    omega
  sig_pre [signWithCacheContract, signWithCacheSig, signSig, abi, VG.AArch64.argRegs]
  simp only [signEntryRd, h5, h6, e0, e1, e2, e3, e4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  refine ⟨sn, True.intro, wr, d1.sub_left keyPrefix, d2.sub_left keyPrefix,
    d3, d4, d5, d6, d7, (d1.sub_left suffix).symm, (d2.sub_left suffix).symm,
    (k1.sub_left ks).sub_right keyPrefix, k2.sub_left ks, k3.sub_left ks,
    k4.sub_left ks, k5.sub_left ks, (k1.sub_left ks).sub_right suffix,
    nkey, n2, n3, n4, n5, nsuffix, Or.inr ⟨?_, cache⟩⟩
  rw [hn]

def rawVerifyK (p : Params) (prepared : Bool) (A : Abi isa) : Contract isa :=
  if prepared then preparedVerifyContract p A 64 else verifyContract p A 64

def rawVerifyBytes (p : Params) (prepared : Bool) : Nat :=
  if prepared then preparedPublicKeyBytes p else p.pkLen

theorem verify_entry_layout {p : Params} {prepared : Bool} {σ : State}
    (pre : (rawVerifyK p prepared abi).pre σ) :
    64 ≤ σ.sp.toNat ∧
    σ.rd = [⟨σ.gpr .x0, rawVerifyBytes p prepared⟩, ⟨σ.gpr .x1, 64⟩, ⟨σ.gpr .x2, p.sigLen⟩] ∧
    σ.wr = [⟨σ.gpr .x3, scratchWords p * 8⟩] ∧
    (below σ.sp 64).Disjoint ⟨σ.gpr .x0, rawVerifyBytes p prepared⟩ ∧
    (below σ.sp 64).Disjoint ⟨σ.gpr .x1, 64⟩ ∧
    (below σ.sp 64).Disjoint ⟨σ.gpr .x2, p.sigLen⟩ ∧
    (below σ.sp 64).Disjoint ⟨σ.gpr .x3, scratchWords p * 8⟩ := by
  cases prepared
  all_goals
    simp only [rawVerifyK, rawVerifyBytes, Bool.false_eq_true, ↓reduceIte] at pre ⊢
    sig_pre [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
      abi, VG.AArch64.argRegs] at pre
    exact ⟨pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.2.2.2.1,
      pre.2.2.2.2.2.2.2.1, pre.2.2.2.2.2.2.2.2.1, pre.2.2.2.2.2.2.2.2.2.1⟩

theorem verify_entry_pre {p : Params} (hp : Sign.Ok3 p) {prepared : Bool} {σ s : State}
    (pre : (rawVerifyK p prepared abi).pre σ)
    (o : Only [.x4, .x5] (pushState .x30 σ) s)
    (h4 : s.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0))
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0)) :
    (verifyWithCacheContract p abi 48).pre
      (s.callEntry.withRegions (verifyEntryRd p s) σ.wr) := by
  cases prepared
  · exact verify_empty_pre pre o (by simpa using h4) h5
  · exact verify_prepared_pre hp pre o h4 h5

theorem verify_entry_covers {p : Params} {prepared : Bool} {σ s : State}
    (pre : (rawVerifyK p prepared abi).pre σ)
    (o : Only [.x4, .x5] (pushState .x30 σ) s)
    (h4 : s.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0))
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0)) :
    Covers (verifyEntryRd p s ++ σ.wr) (s.rd ++ s.wr) := by
  have layout := verify_entry_layout pre
  have e0 : s.gpr .x0 = σ.gpr .x0 := o.get .x0 (by decide)
  have e1 : s.gpr .x1 = σ.gpr .x1 := o.get .x1 (by decide)
  have e2 : s.gpr .x2 = σ.gpr .x2 := o.get .x2 (by decide)
  apply Covers.append
  · apply Covers.of_sub
    intro R hR
    simp only [verifyEntryRd, List.mem_cons, List.not_mem_nil, or_false] at hR
    rw [o.rd, show (pushState .x30 σ).rd = σ.rd from rfl, layout.2.1]
    rcases hR with rfl | rfl | rfl | rfl
    · refine ⟨⟨σ.gpr .x0, rawVerifyBytes p prepared⟩, by simp, 0, ?_, ?_⟩
      · simpa using e0
      · cases prepared <;> simp [rawVerifyBytes, preparedPublicKeyBytes]
    · exact ⟨⟨σ.gpr .x1, 64⟩, by simp, 0, by simpa using e1, Nat.le_refl _⟩
    · exact ⟨⟨σ.gpr .x2, p.sigLen⟩, by simp, 0, by simpa using e2, by change 0 + p.sigLen ≤ p.sigLen; omega⟩
    · refine ⟨⟨σ.gpr .x0, rawVerifyBytes p prepared⟩, by simp,
        (if prepared then p.pkLen else 0), h4, ?_⟩
      rw [h5]
      cases prepared
      · change 0 + (0 : BitVec 64).toNat ≤ p.pkLen
        exact Nat.zero_le _
      · have hm : (BitVec.ofNat 64 (1024 * p.k)).toNat ≤ 1024 * p.k := Nat.mod_le _ _
        simp only [rawVerifyBytes, ↓reduceIte, preparedPublicKeyBytes, n]
        omega
  · rw [o.wr]
    exact Covers.refl _

theorem save_input_bytes {r : Reg} {σ : State} {key : Addr} {len : Nat}
    (hd : (below σ.sp 64).Disjoint ⟨key, len⟩) (hb : len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt (pushState r σ).mem key len = Spec.Sha3.bytesAt σ.mem key len := by
  apply VG.Proof.MlKem.bytesAt_frame (rs := [below σ.sp 16]) ?_ ?_ hb
  · exact Frame.write (r := below σ.sp 16) (Frame.refl _ _) (by simp) _
      (by simp [Region.Contains])
  · intro R hR
    obtain rfl := List.mem_singleton.mp hR
    exact (hd.sub_left (below_sub (by decide) (by decide))).symm

theorem operation_call_bounds {code : Prog isa} (hd : Message.DLe 3 code) :
    16 * code.aarch64Depth + 16 < 2 ^ 64 ∧ 16 * code.aarch64Depth < 2 ^ 64 := by
  have bound := hd.le
  omega

theorem verify_entry_correct {p : Params} (hp : Sign.Ok3 p) {name : String}
    {code : Prog isa} (hv : ∀ σ, (verifyWithCacheContract p abi 48).pre σ →
      ∃ tr t, Exec isa code σ tr t ∧ abiPreserved σ t ∧
        (verifyWithCacheContract p abi 48).post σ t)
    (hd : Message.DLe 3 code) (prepared : Bool) (σ : State)
    (pre : (rawVerifyK p prepared abi).pre σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared) σ tr t ∧
      abiPreserved σ t ∧ (rawVerifyK p prepared abi).post σ t := by
  have layout := verify_entry_layout pre
  have depth := (operation_call_bounds hd).1
  have guard : ∀ R ∈ σ.wr, (below σ.sp 16).Disjoint R := by
    intro R hR
    rw [layout.2.2.1] at hR
    obtain rfl := List.mem_singleton.mp hR
    exact layout.2.2.2.2.2.2.sub_left (below_sub (by decide) (by decide))
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared) σ
      fun t => abiPreserved σ t ∧ (rawVerifyK p prepared abi).post σ t := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.entry
    refine WP.frameReg (Nat.le_trans (by decide) layout.1) guard ?_ (by
      simpa only [Code.aarch64Depth, Nat.zero_max] using depth)
    change WP isa (.seq (.block (operationSetup p false prepared)) (.call name code)) (pushState .x30 σ) _
    refine WP.seq (WP.mono (operationSetup_ok p false prepared (pushState .x30 σ)) fun s hs => ?_)
    have hc := verify_entry_covers pre hs.1 hs.2.1 hs.2.2
    have hcpre := verify_entry_pre hp pre hs.1 hs.2.1 hs.2.2
    have hw : Covers σ.wr s.wr := by rw [hs.1.wr]; exact Covers.refl _
    refine WP.callFV hv hcpre hc hw (fun t hr ht hsp hf hcs hvs post => ?_) (operation_call_bounds hd).2
    refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
    · intro r hR
      by_cases h30 : r = .x30
      · subst r; simp [State.write]
      simp only [State.write, h30, ite_false]
      rw [hcs r hR h30, hs.1.get r (by
        revert hR h30; cases r <;> decide)]
      rfl
    · intro r hR
      exact (hvs r hR).trans (hs.1.vcs r hR)
    · have e0 : s.gpr .x0 = σ.gpr .x0 := hs.1.get .x0 (by decide)
      have e1 : s.gpr .x1 = σ.gpr .x1 := hs.1.get .x1 (by decide)
      have e2 : s.gpr .x2 = σ.gpr .x2 := hs.1.get .x2 (by decide)
      have keySub : Region.Sub (⟨σ.gpr .x0, p.pkLen⟩ : Region)
          ⟨σ.gpr .x0, rawVerifyBytes p prepared⟩ := Region.sub_prefix (by
        cases prepared <;> simp [rawVerifyBytes, preparedPublicKeyBytes])
      have keyB : p.pkLen ≤ 2 ^ 64 := by rcases hp with rfl | rfl | rfl <;> decide
      have sigB : p.sigLen ≤ 2 ^ 64 := by rcases hp with rfl | rfl | rfl <;> decide
      have key := save_input_bytes (r := .x30) (layout.2.2.2.1.sub_right keySub) keyB
      have mu := save_input_bytes (r := .x30) layout.2.2.2.2.1 (by decide)
      have sig := save_input_bytes (r := .x30) layout.2.2.2.2.2.1 sigB
      sig_post [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs] at post
      simp only [e0, e1, e2, hs.1.mem, key, mu, sig] at post
      cases prepared
      all_goals
        simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte]
        sig_post [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
          abi, VG.AArch64.argRegs]
        simpa only [State.write, reduceCtorEq, ite_false] using post
  obtain ⟨tr, t, he, habi, hpost⟩ := main
  exact ⟨tr, t, he, habi, hpost⟩

theorem verify_entry_snapshots {p : Params} (hp : Sign.Ok3 p) {prepared : Bool} {σ s : State}
    (pre : (rawVerifyK p prepared abi).pre σ)
    (o : Only [.x4, .x5] (pushState .x30 σ) s) :
    Spec.Sha3.bytesAt s.mem (s.gpr .x0) p.pkLen = Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) p.pkLen ∧
    Spec.Sha3.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) 64 ∧
    Spec.Sha3.bytesAt s.mem (s.gpr .x2) p.sigLen = Spec.Sha3.bytesAt σ.mem (σ.gpr .x2) p.sigLen := by
  have layout := verify_entry_layout pre
  have e0 : s.gpr .x0 = σ.gpr .x0 := o.get .x0 (by decide)
  have e1 : s.gpr .x1 = σ.gpr .x1 := o.get .x1 (by decide)
  have e2 : s.gpr .x2 = σ.gpr .x2 := o.get .x2 (by decide)
  have keySub : Region.Sub (⟨σ.gpr .x0, p.pkLen⟩ : Region)
      ⟨σ.gpr .x0, rawVerifyBytes p prepared⟩ := Region.sub_prefix (by
    cases prepared <;> simp [rawVerifyBytes, preparedPublicKeyBytes])
  have keyB : p.pkLen ≤ 2 ^ 64 := by rcases hp with rfl | rfl | rfl <;> decide
  have sigB : p.sigLen ≤ 2 ^ 64 := by rcases hp with rfl | rfl | rfl <;> decide
  simp only [e0, e1, e2, o.mem]
  exact ⟨save_input_bytes (layout.2.2.2.1.sub_right keySub) keyB,
    save_input_bytes layout.2.2.2.2.1 (by decide), save_input_bytes layout.2.2.2.2.2.1 sigB⟩

theorem verify_entry_pub {p : Params} (hp : Sign.Ok3 p) {prepared : Bool} {σ τ x y : State}
    (px : (rawVerifyK p prepared abi).pre σ) (py : (rawVerifyK p prepared abi).pre τ)
    (pub : (rawVerifyK p prepared abi).pub σ τ)
    (ox : Only [.x4, .x5] (pushState .x30 σ) x)
    (oy : Only [.x4, .x5] (pushState .x30 τ) y)
    (x4 : x.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0))
    (x5 : x.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0))
    (y4 : y.gpr .x4 = τ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0))
    (y5 : y.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0)) :
    (verifyWithCacheContract p abi 48).pub
      (x.callEntry.withRegions (verifyEntryRd p x) σ.wr)
      (y.callEntry.withRegions (verifyEntryRd p y) τ.wr) := by
  have snapsX := verify_entry_snapshots hp px ox
  have snapsY := verify_entry_snapshots hp py oy
  have base : σ.sp = τ.sp ∧
      leakBytes (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) p.pkLen ++
        Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) 64 ++ Spec.Sha3.bytesAt σ.mem (σ.gpr .x2) p.sigLen) =
      leakBytes (Spec.Sha3.bytesAt τ.mem (τ.gpr .x0) p.pkLen ++
        Spec.Sha3.bytesAt τ.mem (τ.gpr .x1) 64 ++ Spec.Sha3.bytesAt τ.mem (τ.gpr .x2) p.sigLen) ∧
      σ.gpr .x0 = τ.gpr .x0 ∧ σ.gpr .x1 = τ.gpr .x1 ∧ σ.gpr .x2 = τ.gpr .x2 ∧ σ.gpr .x3 = τ.gpr .x3 := by
    cases prepared
    all_goals
      simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte] at pub
      sig_pub [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
        abi, VG.AArch64.argRegs] at pub
      exact pub
  sig_pub [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ox.sp, oy.sp]
    exact congrArg (· - 16) base.1
  · rw [snapsX.1, snapsX.2.1, snapsX.2.2, snapsY.1, snapsY.2.1, snapsY.2.2]
    exact base.2.1
  · exact (ox.get .x0 (by decide)).trans (base.2.2.1.trans (oy.get .x0 (by decide)).symm)
  · exact (ox.get .x1 (by decide)).trans (base.2.2.2.1.trans (oy.get .x1 (by decide)).symm)
  · exact (ox.get .x2 (by decide)).trans (base.2.2.2.2.1.trans (oy.get .x2 (by decide)).symm)
  · exact (ox.get .x3 (by decide)).trans (base.2.2.2.2.2.trans (oy.get .x3 (by decide)).symm)
  · rw [x4, y4, base.2.2.1]
  · rw [x5, y5]

theorem operationSetup_tr {p : Params} (hp : Sign.Ok3 p) (sign prepared : Bool) :
    RelCT isa (SameIn [.x0]) (.block (operationSetup p sign prepared)) (fun _ _ => True) := by
  apply taintRel [.x0] (hc := .block []) (fun _ _ h => ⟨h.2, h.1⟩)
  rcases hp with rfl | rfl | rfl <;> cases sign <;> cases prepared <;>
    simp only [operationSetup, Bool.false_eq_true, ↓reduceIte] <;> taint_decide

def RawVerifyRel (p : Params) (prepared : Bool) (x y : State) : Prop :=
  (rawVerifyK p prepared abi).pre x ∧ (rawVerifyK p prepared abi).pre y ∧
    (rawVerifyK p prepared abi).pub x y

theorem verify_entry_bases {p : Params} {prepared : Bool} {x y : State}
    (h : (rawVerifyK p prepared abi).pub x y) : SameIn [.x0] x y := by
  cases prepared
  all_goals
    simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pub [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
      abi, VG.AArch64.argRegs] at h
    exact ⟨fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.2.2.1, h.1⟩

def VerifyCallRel (p : Params) (prepared : Bool) (x y : State) : Prop :=
  ∃ σ τ, RawVerifyRel p prepared σ τ ∧
    Only [.x4, .x5] (pushed .x30 σ) x ∧ Only [.x4, .x5] (pushed .x30 τ) y ∧
    x.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0) ∧
    x.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0) ∧
    y.gpr .x4 = τ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0) ∧
    y.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0)

theorem operation_narrow {R : List Reg} {σ s : State} (o : Only R (pushed .x30 σ) s) :
    Only R (pushState .x30 σ) (s.withRegions σ.rd σ.wr) :=
  ⟨o.gpr, o.mem, rfl, rfl, o.sp, o.vcs⟩

theorem operation_cover {R : List Reg} {σ s : State} (o : Only R (pushed .x30 σ) s) :
    Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr) := by
  rw [o.rd, o.wr]
  exact Covers.append (Covers.refl _) (push_wr_cover .x30 σ)

theorem verify_entry_ct {p : Params} (hp : Sign.Ok3 p) {name : String} {code : Prog isa}
    (hv : ∀ σ, (verifyWithCacheContract p abi 48).pre σ →
      ∃ tr t, Exec isa code σ tr t ∧ abiPreserved σ t ∧
        (verifyWithCacheContract p abi 48).post σ t)
    (hct : ConstantTime isa (verifyWithCacheContract p abi 48).pre
      (verifyWithCacheContract p abi 48).pub code) (prepared : Bool) :
    ConstantTime isa (rawVerifyK p prepared abi).pre (rawVerifyK p prepared abi).pub
      (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared) := by
  have hs : ∀ x y, RawVerifyRel p prepared x y → x.sp = y.sp :=
    fun _ _ h => (verify_entry_bases h.2.2).2
  have trace : RelCT isa (RawVerifyRel p prepared)
      (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared) (fun _ _ => True) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.entry
    refine frame_tr (R := fun _ _ => True) hs ?_
    change RelCT isa (PushRel .x30 (RawVerifyRel p prepared))
      (.seq (.block (operationSetup p false prepared)) (.call name code)) (fun _ _ => True)
    refine RelCT.seq (R := VerifyCallRel p prepared) (RelCT.postDep
      (RelCT.mono (operationSetup_tr hp false prepared) (fun x y h => ?_) (fun _ _ _ => trivial))
      (fun x y _ => ⟨operationSetup_ok p false prepared x, operationSetup_ok p false prepared y⟩)
      (fun x y x' y' h hx hy => ?_)) ?_
    · rcases h with ⟨σ, τ, h, rfl, rfl⟩
      exact ⟨(verify_entry_bases h.2.2).1, congrArg (· - 16) (hs σ τ h)⟩
    · rcases h with ⟨σ, τ, h, rfl, rfl⟩
      exact ⟨σ, τ, h, hx.1, hy.1, hx.2.1, hx.2.2, hy.2.1, hy.2.2⟩
    · apply RelCT.callEx hv hct
      rintro x y ⟨σ, τ, h, ox, oy, x4, x5, y4, y5⟩
      have nx := operation_narrow ox
      have ny := operation_narrow oy
      refine ⟨verifyEntryRd p x, σ.wr, verifyEntryRd p y, τ.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have px := verify_entry_pre hp h.1 nx x4 x5
        simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
          verifyEntryRd, State.withRegions_gpr] using px
      · have py := verify_entry_pre hp h.2.1 ny y4 y5
        simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
          verifyEntryRd, State.withRegions_gpr] using py
      · have pub := verify_entry_pub hp h.1 h.2.1 h.2.2 nx ny x4 x5 y4 y5
        simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
          verifyEntryRd, State.withRegions_gpr] using pub
      · have cover := verify_entry_covers h.1 nx x4 x5
        change Covers (verifyEntryRd p x ++ σ.wr) (σ.rd ++ σ.wr) at cover
        exact cover.trans (operation_cover ox)
      · rw [ox.wr]; exact push_wr_cover .x30 σ
      · have cover := verify_entry_covers h.2.1 ny y4 y5
        change Covers (verifyEntryRd p y ++ τ.wr) (τ.rd ++ τ.wr) at cover
        exact cover.trans (operation_cover oy)
      · rw [oy.wr]; exact push_wr_cover .x30 τ
  intro x y tx ty x' y' hx hy hpub ex ey
  exact (trace x y tx ty x' y' ⟨hx, hy, hpub⟩ ex ey).1

def rawVerifySat (p : Params) (prepared : Bool) (m : Mem) : State where
  gpr r := match r with | .x0 => 0x10000 | .x1 => 0x20000 | .x2 => 0x30000 | .x3 => 0x40000 | _ => 0
  sp := 0x1000000
  mem := m
  rd := [⟨0x10000, rawVerifyBytes p prepared⟩, ⟨0x20000, 64⟩, ⟨0x30000, p.sigLen⟩]
  wr := [⟨0x40000, scratchWords p * 8⟩]

theorem raw_verify_sat_pre {p : Params} (hp : Sign.Ok3 p) {m : Mem}
    (prepared : Bool) (cache : prepared = true → PreparedPublicKey p m 0x10000) :
    (rawVerifyK p prepared abi).pre (rawVerifySat p prepared m) := by
  cases prepared
  · rcases hp with rfl | rfl | rfl
    all_goals
      simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte]
      sig_pre [verifyContract, verifySig, abi, VG.AArch64.argRegs]
      simp only [rawVerifyBytes, Bool.false_eq_true, ↓reduceIte]
      sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide +kernel
  · have cached := cache rfl
    rcases hp with rfl | rfl | rfl
    all_goals
      simp only [rawVerifyK, ↓reduceIte]
      sig_pre [preparedVerifyContract, preparedVerifySig, abi, VG.AArch64.argRegs]
      simp only [rawVerifyBytes, ↓reduceIte]
      sig_and_intros
      all_goals first | exact cached | rfl | exact Region.disjoint_of_sep (by decide) | decide +kernel

theorem raw_verify_sat {p : Params} (hp : Sign.Ok3 p) (prepared : Bool) :
    ∃ s, (rawVerifyK p prepared abi).pre s := by
  cases prepared
  · exact ⟨rawVerifySat p false (fun _ => 0), raw_verify_sat_pre hp false (by intro h; cases h)⟩
  · have prepPre : (preparePublicKeyContract p abi 80).pre (prepSat p.pkLen p.k) := by
      rcases hp with rfl | rfl | rfl
      all_goals sig_sat_check [preparePublicKeyContract, preparePublicKeySig, prepSat, abi, VG.AArch64.argRegs]
    obtain ⟨_, t, _, _, post⟩ := public_correct hp _ prepPre
    sig_post [preparePublicKeyContract, preparePublicKeySig, abi, VG.AArch64.argRegs] at post
    have cache : PreparedPublicKey p t.mem 0x10000 := post.2
    exact ⟨rawVerifySat p true t.mem, raw_verify_sat_pre hp true (fun _ => cache)⟩

theorem scalar_verify_entry_verified {p : Params} (hp : Sign.Ok3 p) {name : String} {code : Prog isa}
    (hv : Verified target code (verifyWithCacheContract p abi 48)) (hd : Message.DLe 3 code)
    (prepared : Bool) :
    Verified target (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared)
      (rawVerifyK p prepared abi) :=
  ⟨verify_entry_correct hp hv.1 hd prepared, verify_entry_ct hp hv.1 hv.2.1 prepared,
    raw_verify_sat hp prepared⟩

end VG.Proof.MlDsa.AArch64.PreparedKey
