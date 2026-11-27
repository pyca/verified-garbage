module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inv
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEnd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedHintFinish
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedResponse
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLow
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd

/-! ### `MlDsa.AArch64.Sign.OptimizedPairedDepth`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.OptimizedPairedLoopCorrect`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem pairedIter_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) {checks : Prog isa}
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    (hchecks : ∀σ s t,PositiveIB p S σ t s → PairedRoots S s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u => (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ PairedRoots S u)
    {σ s : State} {t : Nat} (h : PositiveIL p S σ t s) (roots : PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.iterWith keccak.callee P p checks)
      s fun u=>PositiveLP p S σ t u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.iterWith
  refine WP.seq (WP.mono (WP.pairedRoots (positiveCommit_ok hP hp h) roots hcommit hP.s64) fun a ⟨ha,ra⟩ => ?_)
  refine WP.seq (WP.mono (WP.pairedRoots (positiveBall_ok hP hp hb ha) ra hball hP.s64) fun b ⟨hball,rb⟩ => ?_)
  refine WP.seq (WP.ite (M := isa) _ (eval_w0 b) (fun he => ?_) fun he => ?_)
  · have h1 : (b.gpr .x0).setWidth 32=1 := by
      rcases hball.r01 with e | e
      · rw [e] at he; exact absurd he (by decide)
      · exact e
    refine WP.mono (hchecks σ b t hball rb h1) fun u ⟨hu,ru⟩ => ?_
    exact WP.pairedRoots (positiveDecEnd hp (paramsOk hp) (lChk_ok hp)
      (hu.elim .inl (fun h => .inr (.inl h)))) ru (Nat.zero_le _) hP.s64
  · refine WP.mono (WP.pairedRoots (positiveBallFailure_ok hp (lChk_ok hp) hball (by simpa using he))
      rb (Nat.zero_le _) hP.s64) fun u ⟨hu,ru⟩ => ?_
    exact WP.pairedRoots (positiveDecEnd hp (paramsOk hp) (lChk_ok hp) (.inr (.inr hu)))
      ru (Nat.zero_le _) hP.s64

theorem pairedSignLoop_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) {checks : Prog isa}
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    (hchecks : ∀σ s t,PositiveIB p S σ t s → PairedRoots S s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u => (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ PairedRoots S u)
    {σ s : State} (h : PositiveIK p S σ s) (roots : PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith keccak.callee P p checks)
      s fun u=>PositiveXS p S σ u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith
  refine WP.seq (WP.mono (WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp) h) roots (Nat.zero_le _) hP.s64)
    fun a ⟨ha,ra⟩ => ?_)
  refine WP.loop (M := isa) (fun n s => ∃t,n=814-t ∧ PositiveIL p S σ t s ∧ PairedRoots S s)
    (fun n s ⟨t,hn,hs,rs⟩ => ?_) 814 a ⟨0,rfl,ha,ra⟩
  refine WP.mono (pairedIter_ok hP hp hb hcommit hball hchecks hs rs) fun u ⟨hu,ru⟩ => ?_
  rcases hu with ⟨hz,hi⟩ | ⟨hz,hx⟩
  · exact .inr ⟨by rw [eval_x9]; simpa using hz,814-(t+1),by have := hs.t_lt; omega_using [hn, this],t+1,rfl,hi,ru⟩
  · exact .inl ⟨by rw [eval_x9,hz]; rfl,hx,ru⟩

end VG.Proof.MlDsa.AArch64.Sign

end

end

/-! ## From `OptimizedDepth.lean` -/

@[expose] public section

/-! ## From `OptimizedPairedDepth.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

theorem pairedCommit_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : Sign.Ok3 p) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.commitWith v.callee (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak := v)
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  have hm := DLe.of_fd C.expandMask.fd C.expandMask.nd
  have hm2 := DLe.of_fd C.expandMaskPair.fd C.expandMaskPair.nd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.outNtt := ⟨by decide +kernel, by lit_decide⟩
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ) := by
    rcases hp3 with rfl|rfl|rfl <;> exact ⟨by decide +kernel, by lit_decide⟩
  have hh : DLe 1 ((Sign.primsWith v.callee).highPack p.γ₂) := by
    rcases hp3 with rfl|rfl|rfl <;>
    (dsimp only [Sign.primsWith,Impl.MlDsa.AArch64.Optimized.HighPack.code]; dle_tac)
  unfold Impl.MlDsa.AArch64.Sign.Optimized.commitWith
  dle_tac
  unfold Impl.MlDsa.AArch64.Sign.Optimized.masks
  split <;> dle_tac

theorem pairedBall_dle (v : Proof.Sha3.AArch64.Permutation) (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.ballAt (Sign.primsWith v.callee)
      (Impl.MlDsa.AArch64.Sign.cLen p) p.τ Impl.MlDsa.AArch64.Sign.cP) := by
  have hb := DLe.of_fd (Sign.prims_okWith (keccak := v)).ball.fd (Sign.prims_okWith (keccak := v)).ball.nd
  dle_tac

theorem pairedInitialization_dle (v : Proof.Sha3.AArch64.Permutation) (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.positiveDecodeWith v.callee (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak:=v)
  have hu := DLe.of_fd C.bitUnpack.fd C.bitUnpack.nd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt := ⟨by decide +kernel, by lit_decide⟩
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  unfold Impl.MlDsa.AArch64.Sign.positiveDecodeWith
  dle_tac

end VG.Proof.MlDsa.AArch64.Message

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

theorem earlyPairedSeq_dle {one two : Nat → Prog isa}
    (h1 : ∀ k, DLe 1 (one k)) (h2 : ∀ k, DLe 1 (two k)) :
    ∀ n a, DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.seqPairedOk one two a n)
  | 0,_ => DLe.block [] rfl
  | 1,a => h1 a
  | n+2,a => DLe.seq (h2 a)
      (DLe.ite (earlyPairedSeq_dle h1 h2 n (a+2)) (DLe.block [] rfl))

theorem pairedChecks_dle (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) := by
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt := ⟨by decide +kernel, by lit_decide⟩
  have hm : DLe 1 (Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true) := ⟨by decide +kernel, by lit_decide⟩
  have hz : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.addNorm := ⟨by decide +kernel, by lit_decide⟩
  have hl : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.subLowNorm := ⟨by decide +kernel, by lit_decide⟩
  have pz : DLe 1 (Impl.MlDsa.AArch64.Optimized.Paired.selected .z) := ⟨by decide +kernel, by lit_decide⟩
  have pr : DLe 1 (Impl.MlDsa.AArch64.Optimized.Paired.selected .r0) := ⟨by decide +kernel, by lit_decide⟩
  have ph : DLe 1 (Impl.MlDsa.AArch64.Optimized.Paired.selected .h) := ⟨by decide +kernel, by lit_decide⟩
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks
  dle_tac
  · apply earlyPairedSeq_dle
    · intro r
      unfold Impl.MlDsa.AArch64.Sign.Optimized.zR
      dle_tac
    · intro r
      unfold Impl.MlDsa.AArch64.Sign.Optimized.zPair
      dle_tac
  · apply earlyPairedSeq_dle
    · intro r
      unfold Impl.MlDsa.AArch64.Sign.Optimized.r0R
      dle_tac
    · intro r
      unfold Impl.MlDsa.AArch64.Sign.Optimized.r0Pair
      dle_tac

theorem pairedSignWith_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : Sign.Ok3 p) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.signWith v.callee (Sign.primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) := by
  have C := Sign.prims_okWith (keccak:=v)
  have hinit := pairedInitialization_dle v p
  have hcommit := pairedCommit_dle v hp3
  have hb := pairedBall_dle v p
  have hc := pairedChecks_dle p
  have hr := DLe.of_fd C.rejNTT.fd C.rejNTT.nd
  have hr4 := DLe.of_fd C.rej4.fd C.rej4.nd
  have hbp := DLe.of_fd C.bitPack.fd C.bitPack.nd
  have hhp := DLe.of_fd C.hintBitPack.fd C.hintBitPack.nd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.canonicalize := ⟨by decide +kernel, by lit_decide⟩
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signWith
  dle_tac

end VG.Proof.MlDsa.AArch64.Message
