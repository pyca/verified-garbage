module

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

abbrev copySignHint : VG.Taint.Hint AArch64.Taint.T :=
  .seq (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x21, .x28]) (.block [])
    (.loop (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x21, .x28]) (.block []))

theorem copy_sign_check (od os : Nat) :
    taint.check (AArch64.Taint.ofRegs [.x21, .x28])
      (Impl.MlDsa.AArch64.PreparedKey.copy (.x28, od) (.x21, os) 1024) copySignHint =
      some (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x21, .x28]) := by
  dsimp only [Impl.MlDsa.AArch64.PreparedKey.copy, copySignHint,
    Impl.MlDsa.AArch64.Call.lea, Impl.MlDsa.AArch64.Call.movV]
  simp only [show ¬(1024 : Nat) = 0 by decide, ↓reduceIte]
  (repeat' split) <;> rfl

theorem copy_sign_tr (od os : Nat) :
    RelCT isa (SameIn [.x21, .x28])
      (Impl.MlDsa.AArch64.PreparedKey.copy (.x28, od) (.x21, os) 1024)
      (SameIn [.x21, .x28]) := by
  intro x y tx ty x' y' h ex ey
  have ha : AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x21, .x28]) x y :=
    ⟨h.2, fun r hr => h.1 r (AArch64.Taint.mem_ofRegs.mp hr)⟩
  obtain ⟨ht, hp⟩ := VG.Taint.check_sound (copy_sign_check od os) ha ex ey
  exact ⟨ht, (fun r hr => hp.2 r (by simpa using
    (show r ∈ ([.x0, .x1, .x2, .x21, .x28] : List Reg) by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp))), hp.1⟩

theorem restoreSecrets_tr (p : Params) :
    RelCT isa (SameIn [.x21, .x28])
      (Impl.MlDsa.AArch64.PreparedKey.Sign.restoreSecrets p) (SameIn [.x21, .x28]) := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Sign.restoreSecrets
  refine RelCT.seq (R := SameIn [.x21, .x28]) ?_
    (RelCT.seq (R := SameIn [.x21, .x28]) ?_ ?_)
  · exact seqR_tr (Q := fun _ => SameIn [.x21, .x28]) p.ℓ 0
      (fun _ _ _ => copy_sign_tr _ _)
  · exact seqR_tr (Q := fun _ => SameIn [.x21, .x28]) p.k 0
      (fun _ _ _ => copy_sign_tr _ _)
  · exact seqR_tr (Q := fun _ => SameIn [.x21, .x28]) p.k 0
      (fun _ _ _ => copy_sign_tr _ _)

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
