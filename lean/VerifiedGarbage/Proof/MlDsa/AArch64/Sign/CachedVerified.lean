import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsForget
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitializationTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedArtifactDepth
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsPrologue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsPrologue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopConcrete
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedCommitmentCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedSignContract

/-! ## From `CachedRestTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- Initialization, bounded rejection, and accepted-output packing retain the
same observable leakage as the signing contract. -/
theorem rest_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (hp : Ok3 p) {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hloop : ∀σ s, PositiveIK p D σ s → PairedRoots D s →
      WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p checks) s
        (fun u=>PositiveXS p D σ u ∧ PairedRoots D u))
    (htloop : RelCT isa (PairedRS p D (LeakEq p 0) (PositiveIK p D))
      (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p checks) (PositiveOX p D)) :
    RelCT isa (PairedRS p D (LeakEq p 0) fun σ s=>IM p D σ s ∧ StaticRoots D s)
      (Impl.MlDsa.AArch64.Sign.Cached.restWith keccak.callee P p checks)
      (RootRS p D (LeakEq p 0) (FS p D)) := by
  refine liftPairedForgetR (fun _ _ _ h rp=>rest_ok hP hp hinit hloop h.1 h.2 rp) ?_
  unfold Impl.MlDsa.AArch64.Sign.Cached.restWith
  have hi := RelCT.mono (paired_trace_frame hinit hP.s64 (positiveInitialization_tr (E:=LeakEq p 0) hP hp))
    (fun _ _ h=>h) (fun _ _ h=>PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)
  refine RelCT.seq hi (RelCT.seq (htloop) ?_)
  unfold ifOk
  refine ifOkElse_tr (fun x y h=>by rw [h.2.1])
    (RelCT.mono (optimizedOutput_tr hP hp (lo := -(q:Int)+1) (hi := (q:Int)-1) (by omega) (by omega)
      (E := fun _ _=>True)) ?_ (fun _ _ h=>h))
    (RelCT.mono nil_tr (fun _ _ h=>h) (fun _ _ _=>trivial))
  rintro x y ⟨⟨⟨⟨σ,τ,ps,pt,pub,_,hx,hy⟩,_⟩,eq,hj⟩,hne⟩
  have ex := x24_one hx.r01 hne
  have ey : y.gpr .x24=1 := eq ▸ ex
  obtain ⟨_,f,fx,fy⟩ := hj ex
  exact ⟨⟨σ,τ,ps,pt,pub,trivial,hx.conversion ex,hy.conversion ey⟩,f,fx,fy⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedLoopCache.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem Mask.transfer {p : Params} {S : Nat} {σ τ s : State} {t : Nat}
    (hσ : PositiveIK p S σ s) (hτ : PositiveIK p S τ s) (h : Mask p σ t s) : Mask p τ t s := by
  have hr : rppOf p σ=rppOf p τ := hσ.rpp.symm.trans hτ.rpp
  simpa only [Mask,Yv,hr] using h

/-- A cached mask is independent of the existential initial-state witness:
all witnesses of the current key invariant have the same private mask seed. -/
def CacheHeld (p : Params) (S t : Nat) (s : State) : Prop :=
  ∀σ,PositiveIK p S σ s → Mask p σ t s

theorem cacheHeld_of {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hk : PositiveIK p S σ s) (h : Mask p σ t s) : CacheHeld p S t s :=
  fun _ hτ=>h.transfer hk hτ

theorem PositiveLP.key {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (h : PositiveLP p S σ t s) : PositiveIK p S σ s := by
  rcases h with ⟨_,h⟩|⟨_,h⟩ <;> exact h.k

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedDepth.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

theorem cachedCommit_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Cached.commit (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak := v)
  have hm := DLe.of_fd C.expandMask.fd
  have hm2 := DLe.of_fd C.expandMaskPair.fd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.outNtt := ⟨by decide +kernel⟩
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ) := by
    rcases hp3 with rfl|rfl <;> exact ⟨by decide +kernel⟩
  have hh : DLe 1 ((Sign.primsWith v.callee).highPack p.γ₂) := by
    dsimp only [Sign.primsWith,Impl.MlDsa.AArch64.Optimized.HighPack.code]
    dle_tac
  have hc : DLe 1 (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*Impl.MlDsa.AArch64.Sign.w1Len p)
      (Impl.MlDsa.AArch64.Sign.cLen p)) := by
    rcases hp3 with rfl|rfl <;> exact ⟨by decide +kernel⟩
  unfold Impl.MlDsa.AArch64.Sign.Cached.commit
  dle_tac

theorem cachedSignWith_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87)
    {checks : Prog isa} (hchecks : DLe 1 checks) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p checks) := by
  have C := Sign.prims_okWith (keccak := v)
  have hc := cachedCommit_dle v hp3
  have hi := pairedInitialization_dle v p
  have hb := pairedBall_dle v p
  have hr := DLe.of_fd C.rejNTT.fd
  have hr4 := DLe.of_fd C.rej4.fd
  have hrtwo : DLe 1 Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code := ⟨by decide +kernel⟩
  have hp := DLe.of_fd C.bitPack.fd
  have hh := DLe.of_fd C.hintBitPack.fd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.canonicalize := ⟨by decide +kernel⟩
  unfold Impl.MlDsa.AArch64.Sign.Cached.signWith
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA
  split <;> dle_tac

theorem cachedPairedSignWith_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp : p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) :=
  cachedSignWith_dle v hp (pairedChecks_dle p)

end VG.Proof.MlDsa.AArch64.Message

end

/-! ## From `CachedCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem sign_correct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) (σ : State)
    (hpre : (signK p D).pre σ) (hroots : StaticRoots D σ) (rp : PairedRoots D σ) {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hloop : ∀σ s, PositiveIK p D σ s → PairedRoots D s →
      WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p checks) s
        (fun u=>PositiveXS p D σ u ∧ PairedRoots D u)) :
    ∃ t s', Exec isa (Impl.MlDsa.AArch64.Sign.Cached.signWith keccak.callee P p checks) σ t s' ∧ abiPreserved σ s' ∧ (signK p D).post σ s' := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf'
  obtain ⟨hsv, -⟩ := hf'
  have main : WP isa (Impl.MlDsa.AArch64.Sign.Cached.signWith keccak.callee P p checks) σ fun s₅ => abiPreserved σ s₅ ∧
      ∃ s₄, FS p D σ s₄ ∧ s₅.gpr .x0 = s₄.gpr .x24 ∧ s₅.mem = s₄.mem := by
    unfold Impl.MlDsa.AArch64.Sign.Cached.signWith
    refine WP.seq (WP.mono (paired_prologue h3 hP.s64 hpre hroots rp) fun s₁ ⟨⟨hs,h15⟩,r1⟩ => ?_)
    refine WP.seq (WP.mono (WP.pairedRoots (CachedMatrix.rooted_expandA_ok hP h3 ha hs h15) r1 (CachedMatrix.expandA_depth hP p) hP.s64) fun s₂ ⟨⟨h₂,hr₂⟩,r2⟩ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (Impl.MlDsa.AArch64.Sign.Cached.restWith keccak.callee P p checks)) s₂ (FS p D σ) from ?_) fun s₄ h₄ => ?_)
    · unfold ifOk
      refine ifOkElse_ok (fun hne => ?_) fun he => ?_
      · have h1 := x24_one h₂.r01 hne
        obtain ⟨ok, fam⟩ := h₂.ok h1
        exact rest_ok hP h3 hinit hloop ⟨h₂.st,ok,fam⟩ hr₂ r2
      · have h0 := x24_zero h₂.r01 he
        exact WP.block_nil ⟨h₂.st, .inl h0, fun h1 => absurd (h1.symm.trans h0) (by decide),
          fun _ => signMu_min_A (h₂.bad h0)⟩
    · exact WP.mono (epi_ok h₄.st.top fun k hk => h₄.st.lay.inR (hsv k hk)) fun s₅ ⟨hg, hr, hm⟩ =>
        ⟨hg, s₄, h₄, hr, hm⟩
  obtain ⟨t, s', he, hF⟩ := main
  obtain ⟨hg, s₄, h₄, hr, hm⟩ := hF
  refine ⟨t, s', he, hg, ?_⟩
  have e23 : pa s₄ (.x23, 0) = σ.gpr .x3 := by
    rw [pa, h₄.st.top.regs (.x23, .x3) (by decide), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  show Outcome _ _ _
  rcases h₄.r01 with h0 | h1
  · exact .inr ⟨by rw [hr, h0]; rfl, h₄.bad h0⟩
  · exact .inl ⟨by rw [hr, h1]; rfl, maxBounds, by rw [hm, ← e23]; exact h₄.ok h1⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedHashTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (callAt sc)
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)

theorem hashCall_tr {p : Params} {S : Nat} {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → Args (hashArgs p) x x1 → Args (hashArgs p) y y1 → ∃ rd wr : List Region,
      k.pre (x1.callEntry.withRegions rd wr) ∧ k.pre (y1.callEntry.withRegions rd wr) ∧
      k.pub (x1.callEntry.withRegions rd wr) (y1.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (callAt n c (hashArgs p)) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ Args (hashArgs p) x x1 ∧ Args (hashArgs p) y y1)
      (block_nomem_tr (glue_nomem (hashArgs p))) (fun x y _ => ⟨hashGlue_ok p x, hashGlue_ok p y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.callEntry.withRegions a.1 a.2) ∧ k.pre (y1.callEntry.withRegions a.1 a.2) ∧
        k.pub (x1.callEntry.withRegions a.1 a.2) (y1.callEntry.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => RelCT.call C.correct C.ct a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)


theorem hashRegions_eq {p : Params} {x y : State} (e : SameB x y) :
    hashReads p x=hashReads p y ∧ hashWrites p x=hashWrites p y := by
  simp only [hashReads,hashWrites]
  rw [e.pa (p:=(.x26,0)) (by decide),e.pa (p:=sc oW1) (by decide),
    e.pa (p:=sc oMS) (by decide),e.pa (p:=sc oCT) (by decide),
    e.pa (p:=t1P) (by decide),e.pa (p:=t4P) (by decide)]
  exact ⟨rfl,rfl⟩

theorem hashReady_tr {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {P : State→State→Prop}
    (hP : ∀x y,P x y→Lay S (sgR p) (sgW p) x ∧ Lay S (sgR p) (sgW p) y ∧ SameB x y) :
    RelCT isa P (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p))
      fun _ _=>True := by
  have C : CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p))
      (commitTailContract abi (p.k*w1Len p) (cLen p) S) := by
    rcases hp with rfl|rfl
    · exact CommitTail.callee65 hS
    · exact CommitTail.callee87 hS
  refine hashCall_tr C fun x y x1 y1 hxy hx hy => ?_
  obtain ⟨Lx,Ly,e⟩ := hP x y hxy
  obtain ⟨hr,hw⟩ := hashRegions_eq (p:=p) e
  refine ⟨hashReads p x,hashWrites p x,hash_pre hp Lx hx,?_,?_,
    (hash_cov hp Lx).1,(hash_cov hp Lx).2,?_,?_⟩
  · rw [hr,hw]; exact hash_pre hp Ly hy
  · sig_pub [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs]
    rw [hx.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
      hx.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
      hx.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
      hx.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
      hx.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
      hx.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),
      hy.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
      hy.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
      hy.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
      hy.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
      hy.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
      hy.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),Args.sp hx,Args.sp hy]
    exact ⟨e.2,e.pa (by decide),e.pa (by decide),e.pa (by decide),
      e.pa (by decide),e.pa (by decide),e.pa (by decide)⟩
  · rw [hr,hw]; exact (hash_cov hp Ly).1
  · rw [hw]; exact (hash_cov hp Ly).2

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedSignTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem sign_ct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : Ok3 p)
    {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hloop : ∀σ s, PositiveIK p D σ s → PairedRoots D s →
      WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p checks) s
        (fun u=>PositiveXS p D σ u ∧ PairedRoots D u))
    (htloop : RelCT isa (PairedRS p D (LeakEq p 0) (PositiveIK p D))
      (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p checks) (PositiveOX p D)) :
    ConstantTime isa (fun s=>(signK p D).pre s ∧ StaticRoots D s ∧ PairedRoots D s)
      (fun x y=>(signK p D).pub x y ∧ RootSymbolsEq x y ∧
        x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR")
      (Impl.MlDsa.AArch64.Sign.Cached.signWith keccak.callee P p checks) := by
  have trace : RelCT isa (WithPaired D (PositiveEntry p D))
      (Impl.MlDsa.AArch64.Sign.Cached.signWith keccak.callee P p checks) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Cached.signWith
    refine RelCT.seq (withPaired_tr (Nat.zero_le _) hP.s64 (positivePro_tr hp))
      (RelCT.seq (withPaired_tr (CachedMatrix.expandA_depth hP p) hP.s64 (CachedMatrix.positiveExpand_tr hP hp)) ?_)
    refine RelCT.seq (R:=LRel D (sgR p) (sgW p)) ?_
      (lrel_tr (fun _ _ h=>h) (by taint_decide))
    unfold ifOk
    refine ifOkElse_tr (P:=WithPaired D (PositiveRA p D)) (fun _ _ h=>by rw [h.1.1.2])
      (RelCT.mono (rest_tr hP hp hinit hloop htloop) ?_
        (fun _ _ h=>h.1.lrel (fun _ _ h=>h.st)))
      (RelCT.mono nil_tr (fun _ _ h=>h) (fun _ _ h=>h.1.1.1.lrel (fun _ _ h=>h.st)))
    rintro x y ⟨⟨⟨⟨⟨σ,τ,ps,pt,pub,hx,hy⟩,eq⟩,rx,ry,re⟩,px,py,pe⟩,hne⟩
    have ex := x24_one hx.r01 hne
    have ey : y.gpr .x24=1 := eq ▸ ex
    obtain ⟨ox,fx⟩ := hx.ok ex
    obtain ⟨oy,fy⟩ := hy.ok ey
    exact ⟨⟨⟨σ,τ,ps,pt,pub,pub_leq pub (expandA_max ox) (expandA_max oy),
      ⟨⟨⟨hx.st,ox,fx⟩,rx⟩,px⟩,⟨⟨⟨hy.st,oy,fy⟩,ry⟩,py⟩⟩,re⟩,pe⟩
  intro x y tx ty x' y' hx hy pub ex ey
  exact (trace _ _ _ _ _ _ ⟨⟨hx.1,hy.1,pub.1,hx.2.1,hy.2.1,pub.2.1⟩,
    hx.2.2,hy.2.2,pub.2.2⟩ ex ey).1

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedHashSetupTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)

/-- Loading the nonce does not make its value public; only the scratch
address contributes to this straight-line block's trace. -/
theorem hashSetup_tr {p : Params} {S : Nat} {P : State→State→Prop}
    (hP : ∀x y,P x y→LRel S (sgR p) (sgW p) x y) :
    RelCT isa P (.block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (2*p.ℓ-1)])
      fun _ _=>True :=
  lrel_tr (hc:=.block []) hP rfl

/-- The complete commitment-plus-cache call has no data-dependent trace. -/
theorem hash_tr {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) :
    RelCT isa (LRel S (sgR p) (sgW p)) (Impl.MlDsa.AArch64.Sign.Cached.hash p)
      fun _ _=>True := by
  have hp3 : Ok3 p := by rcases hp with rfl|rfl <;> simp [Ok3]
  have hr : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl <;> decide
  have ht := seqL (p:=p) (D:=S) (I:=fun _=>True) (J:=fun _=>True)
    (hashSetup_tr (fun _ _ h=>h.1))
    (fun s L _=>WP.mono (hashSetup_run hp3 s (L.inR hr)) fun t ⟨hk,_⟩=>
      ⟨⟨[],postB_of_keep hk.keep (by decide) (by rw [hk.mem]; exact Frame.refl _ _)⟩,trivial⟩)
    (hashReady_tr hp hS (fun _ _ h=>⟨h.1.lx,h.1.ly,h.1.regs,h.1.sp⟩))
  exact RelCT.mono ht (fun _ _ h=>⟨h,trivial,trivial⟩) (fun _ _ h=>h)

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedConcreteCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem selectedSign_correct (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) (σ : State)
    (hpre : (signK p 16).pre σ) (hr : StaticRoots 16 σ) (rp : PairedRoots 16 σ) :
    ∃t s',Exec isa (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) σ t s' ∧
      abiPreserved σ s' ∧ (signK p 16).post σ s' := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  apply sign_correct (keccak:=v) (prims_okWith (keccak:=v)) hp3 σ hpre hr rp
  · have hd := (Message.pairedInitialization_dle v p).le
    change 16 * _ ≤ 16
    omega
  · intro σ s h r
    apply signLoop_concrete_ok (prims_okWith (keccak:=v)) hp ?_ h r
    have hd := (Message.cachedCommit_dle v hp).le
    change 16 * _ ≤ 16
    omega

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedCommitmentTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached digest call preserves the original strict signing relation while
producing both the current commitment and the next attempt's tail mask. -/
theorem hash_root_tr {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {E : State→State→Prop} {t : Nat} :
    RelCT isa (RootRS p S E (PositiveICh p S · t p.k))
      (Impl.MlDsa.AArch64.Sign.Cached.hash p)
      (RootRS p S E fun σ s=>PositiveIC p S σ t s ∧ Mask p σ (t+1) s) := by
  apply liftRootT (fun _ _ h=>⟨h.c.masks.l.st,h.c.masks.l.k.d.roots⟩)
    (fun _ _ _ h=>hash_ok hp hS h)
  exact RelCT.mono (hash_tr hp hS) (fun _ _ h=>h.1) (fun _ _ h=>h)

/-- Cached commitment timing uses only the public attempt index; cached mask and
hash contents remain secret throughout the unchanged signing schedule. -/
theorem commit_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) {E : State→State→Prop} {t : Nat} :
    RelCT isa (RootRS p S E fun σ s=>PositiveIL p S σ t s ∧ (t=0 ∨ Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.commit P p)
      (RootRS p S E fun σ s=>PositiveIC p S σ t s ∧ Mask p σ (t+1) s) := by
  have hp3 : Ok3 p := by
    rcases hp with h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.commit
  exact RelCT.seq (masks_tr hP hp) (RelCT.seq (positiveRows_tr hp3)
    (RelCT.seq (positivePackRows_tr hP hp3) (hash_root_tr hp (by have := hP.sl; omega))))

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedLoopTrace.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem iter_trace {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp0 : p=mlDsa65 ∨ p=mlDsa87) {checks : Prog isa} (hchecks : PairedChecksCT p S checks)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    {t : Nat} (ht : t<814) :
    RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.iter P p checks) (PairedIX p S t) := by
  have hp : Ok3 p := by rcases hp0 with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.iter
  have hct : RelCT isa
      (PairedRS p S (LeakEq p t) fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.commit P p)
      (PairedRS p S (LeakEq p t) (PositiveIC p S · t)) :=
    RelCT.mono (paired_trace_frame hcommit hP.s64 (commit_tr hP hp0))
      (fun _ _ h=>h) (fun _ _ h=>(PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2).mono (fun _ _ h=>h.1))
  refine RelCT.seq hct (RelCT.seq (pairedBall_step_tr hP hp ht hball) ?_)
  refine RelCT.seq (R:=fun x y=>
      (PairedRS p S (LeakEq p t) (fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s) x y ∧ True) ∨
      (PairedRS p S (LeakEq p t) (PositiveEB p S · t) x y ∧ True))
    (RelCT.ite ?_ ?_ ?_)
    (relOr (RelCT.mono (pairedEndPF_tr hp hP.s64) (fun _ _ h=>h.1) (fun _ _ h=>h))
      (RelCT.mono (pairedEndB_tr hp hP.s64) (fun _ _ h=>h.1) (fun _ _ h=>h)))
  · rintro x y ⟨_,he⟩; rw [eval_w0,eval_w0,he]
  · refine RelCT.mono (hchecks t ht) ?_ (fun _ _ h=>.inl ⟨h,trivial⟩)
    rintro x y ⟨⟨hr,eq⟩,hb⟩
    obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hr
    have h1 := x0_one hx.1.r01 hb
    exact ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,h1⟩,hx.2⟩,⟨⟨hy.1,eq.symm.trans h1⟩,hy.2⟩⟩,rs⟩,rp⟩
  · have hf : RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=0)
        (.block (([.movz .x .x24 0 0] : List Instr)++setQ (VG.Impl.MlDsa.AArch64.Call.sc oCNT) 1))
        (PairedRS p S (LeakEq p t) (PositiveEB p S · t)) :=
      RelCT.mono (paired_trace_frame (Nat.zero_le _) hP.s64 (positiveBallFailure_tr hp (lChk_ok hp)))
        (fun _ _ h=>h) (fun _ _ h=>PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)
    refine RelCT.mono hf ?_ (fun _ _ h=>.inr ⟨h,trivial⟩)
    rintro x y ⟨⟨hr,eq⟩,hb⟩
    obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hr
    have h0 := x0_zero hb
    exact ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,h0⟩,hx.2⟩,⟨⟨hy.1,eq.symm.trans h0⟩,hy.2⟩⟩,rs⟩,rp⟩


end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedLoopTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The original leakage relation remains unchanged. Cache correctness is
an invariant of each execution, not additional observable information. -/
theorem iter_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) (h16 : 16≤S)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    {t : Nat} (ht : t<814) :
    RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.iter P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (fun x y=>PairedIX p S t x y ∧ CacheHeld p S (t+1) x ∧ CacheHeld p S (t+1) y) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  have hchecks : PairedChecksCT p S (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) := by
    intro t ht
    apply positivePairedChecks_tr hp3 (ksChk_ok hp3) h16 hP.s64
    intro σ τ he hs ht'
    exact leq_pass (paramsOk hp3) he ht hs ht'
  intro x y tx ty x' y' hr ex ey
  obtain ⟨eq,hi⟩ := iter_trace hP hp hchecks hcommit hball ht _ _ _ _ _ _ hr ex ey
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := hr.1.1
  obtain ⟨_,u,eu,hu,ru,cu⟩ := iter_ok hP hp3 (bChk_ok hp3) (commit_correct hP hp hcommit)
    hx.1.1 hx.2 hx.1.2
  obtain ⟨_,v,ev,hv,rv,cv⟩ := iter_ok hP hp3 (bChk_ok hp3) (commit_correct hP hp hcommit)
    hy.1.1 hy.2 hy.1.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨eq,hi,cacheHeld_of (PositiveLP.key hu) cu,cacheHeld_of (PositiveLP.key hv) cv⟩

theorem signLoop_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) (h16 : 16≤S)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S) :
    RelCT isa (PairedRS p S (LeakEq p 0) (PositiveIK p S))
      (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (PositiveOX p S) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.signLoop
  refine RelCT.seq (liftPairedR (J:=fun σ s=>PositiveIL p S σ 0 s)
    (fun _ _ _ h roots=>WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp3) h) roots (Nat.zero_le _) hP.s64)
    (lrel_tr (fun _ _ h=>h.root.1.lrel (fun _ _ h=>h.d.im.st)) (by taint_decide))) ?_
  refine RelCT.mono (RelCT.loop (M:=isa)
    (fun n x y=>∃t,n=814-t ∧ PairedRS p S (LeakEq p t)
      (fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s)) x y)
    (fun n=>?_) 814)
    (fun _ _ h=>⟨0,rfl,h.mono (fun _ _ h=>⟨h,.inl rfl⟩)⟩) (fun _ _ h=>h)
  intro x y tx ty x' y' ⟨t,hn,hr⟩ ex ey
  have ht : t<814 := by obtain ⟨_,_,_,_,_,_,hx,_⟩ := hr.1.1; exact hx.1.1.t_lt
  obtain ⟨htr,hi,cx,cy⟩ := iter_tr hP hp h16 hcommit hball ht _ _ _ _ _ _ hr ex ey
  refine ⟨htr,by rw [eval_x9,eval_x9,hi.1.1],fun h=>hi.1.2.2 (x9_zero h),fun h=>?_⟩
  have hnxt := hi.next (x9_ne h)
  obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hnxt
  exact ⟨814-(t+1),by omega,t+1,rfl,
    ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,.inr (cx σ hx.1.k)⟩,hx.2⟩,
      ⟨⟨hy.1,.inr (cy τ hy.1.k)⟩,hy.2⟩⟩,rs⟩,rp⟩⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached signer uses the original public signing contract. -/
theorem sign_verified_of_loop (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    (htloop : RelCT isa (PairedRS p 16 (LeakEq p 0) (PositiveIK p 16))
      (Impl.MlDsa.AArch64.Sign.Cached.signLoop (primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) (PositiveOX p 16)) :
    Verified AArch64.target
      (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (signContract p (abi.withConsts pairedSignRootConsts) signStack) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  apply Verified.of_correct (k:=pairedSignK p signStack)
  · intro σ h
    exact selectedSign_correct v hp σ h.1 h.2.1 h.2.2
  · apply sign_ct (keccak:=v) (prims_okWith (keccak:=v)) hp3
    · have hd := (Message.pairedInitialization_dle v p).le
      change 16 * _ ≤ 16
      omega
    · intro σ s h r
      apply signLoop_concrete_ok (prims_okWith (keccak:=v)) hp ?_ h r
      have hd := (Message.cachedCommit_dle v hp).le
      change 16 * _ ≤ 16
      omega
    · exact htloop
  · exact pairedSignK_implies_spec hp3

theorem sign_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) :
    Verified AArch64.target
      (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (signContract p (abi.withConsts pairedSignRootConsts) signStack) := by
  apply sign_verified_of_loop v hp
  apply signLoop_tr (prims_okWith (keccak:=v)) hp (by decide)
  · have hd := (Message.cachedCommit_dle v hp).le
    change 16 * _ ≤ 16
    omega
  · have hd := (Message.pairedBall_dle v p).le
    change 16 * _ ≤ 16
    omega

end VG.Proof.MlDsa.AArch64.Sign.Cached

end
