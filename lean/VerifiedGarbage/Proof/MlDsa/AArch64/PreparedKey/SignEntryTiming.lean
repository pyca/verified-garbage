module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.SignRest
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsPrologue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedArtifactDepth
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttVerified
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Entry
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Verified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Base
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AddrArith
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Fintype.Fin
public import VerifiedGarbage.Impl.MlDsa.AArch64.Message
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Verify
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Layout
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inv
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseLCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.VerifyKeyRow
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Final
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedState
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedHintPack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedDot
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedTimingBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Optimized
import VerifiedGarbage.Proof.MlDsa.DecideAt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSingleCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductCallTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotCallTiming
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Cmp
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Lay
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSat
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedSamples
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRel
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifySat
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MatrixMask
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCallTwo
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp4
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MatrixMask
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Call4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Hash
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyPre
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitializationTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsForget
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
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
import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Sign
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitialization
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.MlDsa.Sign.Iter
public import VerifiedGarbage.Impl.MlDsa.AArch64.Call
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
public import VerifiedGarbage.Spec.MlDsa

/-! ### `MlDsa.AArch64.Verify.OptimizedSelected`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Verify.OptimizedNtt`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Verify.Optimized
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.KeyGen (ifp ifn)

theorem nttZ_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {i : Nat} (hi : i<p.ℓ)
    (hs : SC p S σ h A' c0 q i false 0 s) :
    WP isa (forward (zP p i)) s (SC p S σ h A' c0 q (i+1) false 0) := by
  have L := hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hz := hs.z i hi
  simp only [Stored,decide_eq_false_iff_not.mpr (Nat.lt_irrefl i),Bool.false_eq_true,↓reduceIte,
    ifn (Nat.lt_irrefl i)] at hz
  have hr : inB (vR p++vW p) (zP p i) 1024=true := by vlayd
  have hw : inB (vW p) (zP p i) 1024=true := by vlayd
  refine WP.mono_syms (Sign.positiveNttAt_layout L hr hw
    ⟨hs.roots.nttTableAt (L.inW hw),hs.roots.forward.readable⟩ hz.1)
    fun t ⟨hP,x',hv⟩ hy=>?_
  refine ⟨hs.vc.step hF hp hP (by unfold vcChk;vlay),
    hs.roots.step_layout L hP hy (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact hw),
    hs.hh,L.keepHint hP (by vlayd) hs.hint,hs.nok,hs.gd,
    fun r' hr' c hc'=>L.keepPoly hP (by have := ar_lt hr' hc';vlay) (hs.a r' hr' c hc'),
    fun i' hi'=>?_,stored_keep L hP (by vlayd) hs.c,
    fun _ h=>absurd h (Nat.not_lt_zero _),x'.trans hs.x24⟩
  by_cases he : i'=i
  · subst i'
    simp only [Stored,decide_eq_true_eq.mpr (Nat.lt_succ_self i),↓reduceIte]
    rw [ifp (Nat.lt_succ_self i),hP.pa (show Reg.x28∈keptRegs by decide)]
    rw [hz.2] at hv
    exact hv
  · have hv' := stored_keep L hP (by vlayd) (hs.z i' hi')
    have hh : (i'<i+1)=(i'<i) := propext (by omega_using [he])
    simpa only [hh] using hv'

theorem nttC_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool}
    (hs : SC p S σ h A' c0 q p.ℓ false 0 s) :
    WP isa (forward (cP p)) s (SC p S σ h A' c0 q p.ℓ true 0) := by
  have L := hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hz : PolyIs s.mem (pa s (cP p)) c0 := hs.c
  have hr : inB (vR p++vW p) (cP p) 1024=true := by vlayd
  have hw : inB (vW p) (cP p) 1024=true := by vlayd
  refine WP.mono_syms (Sign.positiveNttAt_layout L hr hw
    ⟨hs.roots.nttTableAt (L.inW hw),hs.roots.forward.readable⟩ hz.1)
    fun t ⟨hP,x',hv⟩ hy=>?_
  refine ⟨hs.vc.step hF hp hP (by unfold vcChk;vlay),
    hs.roots.step_layout L hP hy (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact hw),
    hs.hh,L.keepHint hP (by vlayd) hs.hint,hs.nok,hs.gd,
    fun r' hr' c hc'=>L.keepPoly hP (by have := ar_lt hr' hc';vlay) (hs.a r' hr' c hc'),
    fun i hi=>stored_keep L hP (by vlayd) (hs.z i hi),?_,
    fun _ h=>absurd h (Nat.not_lt_zero _),x'.trans hs.x24⟩
  change PosPolyIs t.mem (pa t (cP p)) (ntt c0)
  rw [hP.pa (show Reg.x28∈keptRegs by decide)]
  rw [hz.2] at hv
  exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedRowReady`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Verify (wRow)
open VG.Proof.MlDsa.Arith.Montgomery
theorem product_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (_hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (_hw : W p σ A' r s)
    (ht : PosPolyIs s.mem (pa s (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)) :
    MontProduct.Ready (tm2P p) (cP p) (tmP p) s := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : PosPolyIs s.mem (pa s (cP p)) (ntt c0) := hs.c
  have ro : inB (vR p++vW p) (tm2P p) 1024=true := by vlayd
  have ra : inB (vR p++vW p) (cP p) 1024=true := by vlayd
  have rb : inB (vR p++vW p) (tmP p) 1024=true := by vlayd
  have wo : inB (vW p) (tm2P p) 1024=true := by vlayd
  have ready : MontProduct.Ready (tm2P p) (cP p) (tmP p) s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.disj (by vlayd),L.disj (by vlayd),hc.bound,ht.bound,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  exact ready

theorem inverse_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (_hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (scale montgomeryRInv (Diff p σ A' c0 r))) :
    Inverse.InverseSingleReady (wP p) s := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have rd : inB (vR p++vW p) (wP p) 1024=true := by vlayd
  have wr : inB (vW p) (wP p) 1024=true := by vlayd
  have held : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") := by
    intro j hj
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (hs.roots.inverse.held j hj).trans (eq _ _ (by rw [InverseTable.expandedWords_length];exact hj))
  have ready : Inverse.InverseSingleReady (wP p) s :=
    ⟨held,hs.roots.inverse.apart_write (L.inW wr),hw.1,
      Covers.cons hs.roots.inverse.readable (L.cR rd),L.cW wr⟩
  exact ready

theorem hintPack_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (wRow p (vPk p σ) (vSig p σ) A' (ntt c0) r)) :
    UseHintPack.CallReady (rowP p r) (hP p r) (wP p) p.γ₂ s := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hrow : w1Len p*r+w1Len p≤p.k*w1Len p := by
    rw [←Nat.mul_succ,Nat.mul_comm p.k];exact Nat.mul_le_mul_left _ hr
  have hkw:=hF.w1
  have ro : inB (vR p++vW p) (rowP p r) (w1Len p)=true := by
    rcases hF.wl with he|he <;> vlay [he]
  have ra : inB (vR p++vW p) (hP p r) 1024=true := by vlayd
  have rb : inB (vR p++vW p) (wP p) 1024=true := by vlayd
  have wo : inB (vW p) (rowP p r) (w1Len p)=true := by
    rcases hF.wl with he|he <;> vlay [he]
  have plen : UseHintPack.packLen p.γ₂=w1Len p := rfl
  have ready : UseHintPack.CallReady (rowP p r) (hP p r) (wP p) p.γ₂ s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,
      L.disj (by rw [plen];rcases hF.wl with he|he <;> vlay [he]),
      L.disj (by rw [plen];rcases hF.wl with he|he <;> vlay [he]),
      Round.isG_of_mem hF.g2.1,hw.1,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  exact ready

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedFinish`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt Bounds minBounds rejNTTPoly sampleInBall simpleBitPack verifyMu normRq normR)
open VG.Proof.MlDsa (polyAt Reduced PolyIs HintIs)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlDsa.Verify (w1Row aSeed)

/-- Final digest while preserving the optimized representation invariant. -/
abbrev SCH (p : Params) (S : Nat) (σ s : State) : Prop :=
  ∃ h A' c0 q, SC p S σ h A' c0 q p.ℓ true p.k s ∧
    bytesAt s.mem (pa s (sc oCT)) p.ctildeLen=Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen

theorem rows_bytes {S : Nat} {p : Params} {σ : State} {h : List (Vector Bool Spec.MlDsa.n)} {A' : Nat → Nat → Poly} {c0 : Poly}
    {q : Bool} {s : State} (hs : SC p S σ h A' c0 q p.ℓ true p.k s) :
    Proof.MlKem.AArch64.pbytes s ⟨.x28, oP (p.k * p.ℓ + 0), p.k * w1Len p⟩ = w1Enc p σ h A' c0 := by
  show bytesAt s.mem (s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + 0))) (p.k * w1Len p) = _
  rw [show p.k * w1Len p = w1Len p * p.k from Nat.mul_comm _ _, Proof.MlDsa.KeyGen.bytesAt_pieces]
  exact flatMap_congr' fun r hr => hs.rows r (List.mem_range.mp hr)

theorem hash_vpiece {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) {p : Params} (hF : VFacts p) :
    VPiece p S (SCx p S p.ℓ true p.k) (SCH p S) ((shake256With keccak.callee) (hIns p) [⟨.x28, oCT, p.ctildeLen⟩]) := by
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, vrel_of (Q := VTwo p S) (hash_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => vc_two hF p₁ p₂ pub h₁.vc h₂.vc⟩
  have L := hs.vc.lay hF hp
  refine WP.mono_syms (shake_ok h16 hSl L (by simp) (hash_chk hF)) fun s' ⟨hP', x', ho⟩ hy => ⟨h, A', c0, q, ?_, ?_⟩
  · exact hs.keep hF hp hP' (by scchks hF (Nat.le_refl _)) hy (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl
      all_goals have := hF.ct.2;have := hF.scr;have := hF.k;have := hF.l;have := hF.kl
      all_goals vlay) x'
  · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at ho
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide), ho, rows_bytes hs]
    refine congrArg (Spec.MlDsa.H · p.ctildeLen) (congrArg (· ++ _) ?_)
    show bytesAt s.mem (s.gpr .x26 + BitVec.ofNat 64 0) 64 = _
    exact hs.vc.mu

/-! ## The comparison -/

theorem cmp_vpiece {S : Nat} {p : Params} (hF : VFacts p) :
    VPiece p S (SCH p S) (VFin p) (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen) := by
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hH⟩ => ?_, vrel_of (Q := VTwo p S) (cmp_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => vc_two hF p₁ p₂ pub h₁.vc h₂.vc⟩
  have L := hs.vc.lay hF hp
  have := hF.ct.2; have := hF.sig; have := hF.scr; have := hF.k; have := hF.l; have := hF.kl
  refine WP.mono (cmpAnd_ok L (by omega_arith) (by omega_arith) (by vlayd) (by vlayd)) fun s' ⟨hP', x'⟩ => ⟨?_, ?_⟩
  · exact hs.vc.step hF hp hP' (by unfold vcChk; vlayd)
  · rw [hH, ctOf_eq hF hs.vc, hs.x24] at x'
    have e : s'.gpr .x24 = flag (q = true ∧ Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen = ctOf p σ) := by
      rw [x', and_flag (P := q = true)
        (Q := Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen = ctOf p σ) _ (by split <;> rfl)]
    obtain ⟨hA1, hA0⟩ := hs.gd
    cases q with
    | false =>
      refine .inr ⟨by rw [e]; exact ifn (fun h => Bool.false_ne_true h.1) _ _, ?_⟩
      rcases hA0 rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
      · show verifyMu p minBounds _ _ _ ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_rej_none minBounds _ _ hs.hh hr hc hn']; nofun
      · show verifyMu p minBounds _ _ _ ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_ball_none minBounds _ _ hs.hh (Option.map_eq_none_iff.mp hn')]; nofun
    | true =>
      obtain ⟨hA, hB⟩ := hA1 rfl
      obtain ⟨nA, hnA⟩ := Proof.MlDsa.Verify.common_bound (P := fun r n => ∀ c < p.ℓ,
          rejNTTPoly n (aSeed (vPk p σ) r c) = some (A' r c))
        (fun _ _ _ hle h c hc => Proof.MlDsa.Verify.rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
          Proof.MlDsa.Verify.common_bound (P := fun c n => rejNTTPoly n (aSeed (vPk p σ) r c) = some (A' r c))
            (fun _ _ _ hle h => Proof.MlDsa.Verify.rejNTTPoly_mono hle h) p.ℓ fun c hc =>
              let ⟨b, hb⟩ := hA r hr c hc; ⟨b.rejNTT, hb⟩
      obtain ⟨bB, hbB⟩ := hB
      obtain ⟨cc, hcc, hcc'⟩ := Option.map_eq_some_iff.mp hbB
      have hl : h.length = p.k := hs.hint.1
      have ev := Proof.MlDsa.Verify.verifyMu_rows p ⟨0, 0, nA, bB.ball⟩ (vPk p σ) (vMu σ) (vSig p σ) hs.hh hl hnA
        hcc
      rw [decide_eq_true ((Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1 _).mpr hs.nok), hcc', Bool.true_and,
        ← hF.g2.2] at ev
      by_cases hE : Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen = ctOf p σ
      · exact .inl ⟨by rw [e]; exact ifp (show true = true ∧ _ from ⟨rfl, hE⟩) _ _, ⟨_, ev.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
      · exact .inr ⟨by rw [e]; exact ifn (fun h : true = true ∧ _ => hE h.2) _ _,
          false_ne (ev.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩


/-- Final hashing and comparison use no transformed z/c representation. -/
theorem finish_vpiece {S : Nat} (h16 : 16≤S) (hS : S<2^64) {p : Params} (hF : VFacts p) :
    VPiece p S (SCx p S p.ℓ true p.k) (VFin p)
      (.seq (shake256With keccak.callee (hIns p) [⟨.x28,oCT,p.ctildeLen⟩])
        (cmpAnd (sc oCT) (.x27,0) p.ctildeLen)) :=
  (hash_vpiece h16 hS hF).seq (cmp_vpiece hF)

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedSamplesDepth`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Message

/-- Replacing scalar rejection tails by the resident pair adds no stack depth. -/
theorem samples_depth {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) :
    16*(Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p).aarch64Depth≤S := by
  have h1 : DLe (S/16) P.rejNtt := ⟨by have := hP.rejNtt.fd; omega_using [this], hP.rejNtt.nd⟩
  have h4 : DLe (S/16) P.rej4 := ⟨by have := hP.rej4.fd; omega_using [this], hP.rej4.nd⟩
  have hb : DLe (S/16) P.ball := ⟨by have := hP.ball.fd; omega_using [this], hP.ball.nd⟩
  have h2 : DLe (S/16) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code := by
    have hd : Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code.aarch64Depth=0 := by decide +kernel
    exact ⟨by rw [hd];omega_using [], by lit_decide⟩
  have hd : DLe (S/16) (Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p) := by
    unfold Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples
      Impl.MlDsa.AArch64.Verify.OptimizedSamples.expAll
    split
    · unfold Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4
        Impl.MlDsa.AArch64.Verify.OptimizedSamples.tail2
        Impl.MlDsa.AArch64.Optimized.MatrixMask.code
      dle_tac
    · unfold Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4
        Impl.MlDsa.AArch64.Optimized.MatrixMask.code
      dle_tac
  have := hd.le
  omega_using [this]

theorem samples_noDit {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params)  :
    (Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p).all (fun i => !i.touchesDit) = true := by
  have h1 : DLe (S/16) P.rejNtt := ⟨by have := hP.rejNtt.fd; omega_using [this], hP.rejNtt.nd⟩
  have h4 : DLe (S/16) P.rej4 := ⟨by have := hP.rej4.fd; omega_using [this], hP.rej4.nd⟩
  have hb : DLe (S/16) P.ball := ⟨by have := hP.ball.fd; omega_using [this], hP.ball.nd⟩
  have h2 : DLe (S/16) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code := by
    have hd : Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code.aarch64Depth=0 := by decide +kernel
    exact ⟨by rw [hd];omega_using [], by lit_decide⟩
  have hd : DLe (S/16) (Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p) := by
    unfold Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples
      Impl.MlDsa.AArch64.Verify.OptimizedSamples.expAll
    split
    · unfold Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4
        Impl.MlDsa.AArch64.Verify.OptimizedSamples.tail2
        Impl.MlDsa.AArch64.Optimized.MatrixMask.code
      dle_tac
    · unfold Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4
        Impl.MlDsa.AArch64.Optimized.MatrixMask.code
      dle_tac
  exact hd.nd

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedSamplesFourTiming`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Verify.OptimizedSamplesFour`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Bounds rejNTTPoly minBounds)
open VG.Proof.MlDsa (Reduced polyAt coeffAt poly4 seed4)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (masked_one masked_zero)

theorem vcall4_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ : State} (hp : vPre p S σ) {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) {s : State} (h : VS p σ (4*g) 4 s) :
    WP isa (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
      (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (4*g)) 1024))) s (VA p σ (4*g+4)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  refine WP.seq (WP.mono (rej4At_ok hP.s64 hP.rej4 L
    (seed := sc oSA4) (a := aP (4*g)) (ss := sc (oR4 p)) (by unfold rej4Chk; vlayd))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide) (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by rw [h20.get .x0]; exact hr01
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.MatrixMask.mask_ok L20 (a := aP (4*g)) (N := 64) (by decide) (by decide) (by vlayd) (by vlayd) hr20) fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  have e2 : pa s2 (aP (4*g)) = pa s (aP (4*g)) := sc_pa hP2 _
  have e20 : pa s20 (aP (4*g)) = pa s2 (aP (4*g)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 4,∀ i < 256,coeffAt s3.mem (poly4 (pa s (aP (4*g))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (aP (4*g))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega_using [hk, hi])
  have e3 : ∀ k,pa s3 (aP (4*g+k)) = poly4 (pa s (aP (4*g))) k := fun k => by rw [pa_poly4,sc_pa hP13]
  obtain ⟨q,hq,h1,h0⟩ := h.va.ok
  have hA : ∀ e' < 4*g,polyAt s3.mem (pa s3 (aP e')) = polyAt s.mem (pa s (aP e')) := fun e' he' => L.keepPolyAt hP13 (by vlay)
  refine ⟨h.va.vz.keep hF hp hP13 (by vzchk hF),h.va.nok,by rw [L.keepBytes hP13 (by vlayd)]; exact h.va.rho,
    fun e' he' => ?_,q && ((s2.gpr .x0).setWidth 32 == 1),?_,fun hq' e' he' => ?_,fun hq' => ?_⟩
  · by_cases hlt : e' < 4*g
    · exact L.keepRed hP13 (by vlay) (h.va.red e' hlt)
    · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega_using [hlt]⟩
      rw [e3]
      by_cases hret : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one hret (hco4 k (by omega_using [he']))).2 (hred hret k (by omega_using [he']))
      · exact (masked_zero hret (hco4 k (by omega_using [he']))).1
  · rw [k3.get .x24,e24,h24,hq,and_flag _ (Q := (s2.gpr .x0).setWidth 32 = 1)
      (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true,beq_iff_eq] at hq'
    by_cases hlt : e' < 4*g
    · obtain ⟨b,hb⟩ := h1 hq'.1 e' hlt
      exact ⟨b,by rw [hb,hA e' hlt]⟩
    · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega_using [hlt]⟩
      rcases hout with ⟨_,hb⟩ | ⟨hret,_⟩
      · obtain ⟨b,hb⟩ := hb k (by omega_using [he'])
        exact ⟨b,by rw [e3,(masked_one hq'.2 (hco4 k (by omega_using [he']))).1,← vseed4_eq h (by omega_using [he'])]; exact hb⟩
      · rw [hq'.2] at hret; exact absurd hret (by decide)
  · cases hqq : q
    · obtain ⟨e',he',hn⟩ := h0 hqq; exact ⟨e',by omega_using [he'],hn⟩
    · rw [hqq] at hq'
      simp only [Bool.true_and,beq_eq_false_iff_ne,ne_eq] at hq'
      rcases hout with ⟨hret,_⟩ | ⟨_,k,hk,hn⟩
      · exact absurd hret hq'
      · exact ⟨4*g+k,by omega_using [hk],by rw [← vseed4_eq h hk]; exact hn⟩


end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem matrixMask_taint : ∀j<80,∀n∈[256,512,1024],
    (taint.check (Taint.ofRegs [.x28]) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (sc (oP j)) n)
      (VG.Taint.hintOf taint (Taint.ofRegs [.x28]) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (sc 0) n))).isSome=true := by
  decide +kernel

theorem vcall4_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : VPiece p S (VS p · (4*g) 4) (VA p · (4*g+4))
      (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g))) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (4*g)) 1024))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => vcall4_ok hP hF hp hg h,
    vrel_of (Q := fun x y => VTwo p S x y ∧ bytesAt x.mem (pa x (sc oSA4)) 136 = bytesAt y.mem (pa y (sc oSA4)) 136) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc,by
        rw [h.seeds,h'.seeds]; simp only [seedOf,(vPub_eq hq).2.1]⟩)⟩
  have hc : rej4Chk (vR p) (vW p) (sc oSA4) (aP (4*g)) (sc (oR4 p)) = true := by unfold rej4Chk; vlayd
  have ok := fun x (L : Lay S (vR p) (vW p) x) => WP.mono (rej4At_ok hP.s64 hP.rej4 L hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  have tail : RelCT isa (VTwo p S) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (4*g)) 1024)) fun _ _ => True := by
    refine RelCT.seq (VTwo.step (fun _ _ h => h) (block_nomem_tr fun i hi _ => by
      simp only [and24,List.mem_singleton] at hi; subst hi; rfl) ?_)
      (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (matrixMask_taint (4*g) (by omega_using [hg, hkl]) 1024 (by simp)))
    have f := fun z => WP.mono (and24_ok z) fun z' ⟨o,_⟩ =>
      (⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩ : ∃ W,PostB S z z' W)
    exact fun x y _ => ⟨f x,f y⟩
  exact RelCT.seq (VTwo.step (fun _ _ h => h.1)
    (rej4At_tr hP.rej4 (vOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) tail

theorem expA4_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : VPiece p S (VA p · (4*g)) (VA p · (4*g+4)) (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4 P p g) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4
  refine VPiece.seq (VPiece.mono
    (VPiece.seqR (I := fun j σ s => VS p σ (4*g) j s) 4 0 (fun j _ hj => vslot_piece hF hg (by omega_using [hj])))
      (fun _ _ _ h => ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
      (fun _ _ _ h => by simpa using h)) (vcall4_piece hP hF hg)

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedSamplesTwo`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Bounds rejNTTPoly minBounds)
open VG.Proof.MlDsa (Reduced polyAt coeffAt poly4 seed4)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (masked_one masked_zero)

open VG.Proof.MlDsa.AArch64.KeyGen.Optimized

theorem vslot2_ok {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ)
    {e j : Nat} (he : e+2 ≤ p.k*p.ℓ) (hj : j < 2) {s : State} (h : VS p σ e j s) :
    WP isa (seedSlot4 p e j) s (VS p σ e (j+1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  unfold seedSlot4
  refine WP.seq (WP.mono (copySeed4_generic L (by vlayd) (by vlayd) (by vlayd)) fun s1 ⟨hP1,hk1,hb1⟩ => ?_)
  have h1 := h.va.keep hF hp hP1 (by vachk hF) (hk1.get .x24)
  have L1 := h1.vz.vc.lay hF hp
  unfold setSR
  refine WP.mono (vsetTwo_ok L1 (o := oSA4+34*j+32) (a := (e+j)%p.ℓ) (b := (e+j)/p.ℓ)
    (by dsimp only [oSA4]; omega_arith) (by vlayd) (by vlayd)) fun t ⟨hP2,hk2,hb2⟩ => ?_
  refine ⟨h1.keep hF hp hP2 (by vachk hF) (hk2.get .x24),fun k hk => ?_⟩
  by_cases heq : k = j
  · subst k
    rw [bytes34,L1.keepBytes hP2 (by vlayd),sc_pa hP2,sc_pa hP1,hb1,h.va.rho,
      sc_add,← sc_pa hP1,hb2,seedOf,Proof.MlDsa.Verify.aSeed,integerToBytes_one,integerToBytes_one,List.append_assoc]
    rfl
  · rw [L1.keepBytes hP2 (by vlayd),L.keepBytes hP1 (by vlayd)]
    exact h.done k (by omega_arith)

theorem vslot2_piece {p : Params} (hF : VFacts p) {S e j : Nat} (he : e+2 ≤ p.k*p.ℓ) (hj : j < 2) :
    VPiece p S (VS p · e j) (VS p · e (j+1)) (seedSlot4 p e j) :=
  ⟨fun _ _ hp h => vslot2_ok hF hp he hj h,
    vrel_of (Q := VTwo p S) (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (slot_taint p e (by omega_arith)))
      fun _ _ _ _ hp hp' hq h h' => vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc⟩

theorem vseed2_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : VS p σ e 2 s) {k : Nat} (hk : k < 2) :
    seed4 s.mem (pa s (sc oSA4)) k = seedOf p σ (e+k) := by
  unfold seed4
  rw [show pa s (sc oSA4)+BitVec.ofNat 64 (34*k) = pa s (sc (oSA4+34*k)) from sc_add _ _ _]
  exact h.done k hk

theorem vcall2_ok {S : Nat} (hS : S<2^64) {cd : Prog isa} {nm : String}
    (C : CalleeOk S cd (VG.Proof.MlDsa.rejNTT2Contract AArch64.abi S)) {p : Params} (hF : VFacts p)
    {σ : State} (hp : vPre p S σ) {e : Nat} (he : e+2 ≤ p.k*p.ℓ) {s : State} (h : VS p σ (e) 2 s) :
    WP isa (.seq (callAt nm cd (rej2Args (sc oSA4) (aP e) (sc (oR4 p))))
      (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512))) s (VA p σ (e+2)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  refine WP.seq (WP.mono (rej2At_ok hS C L
    (seed := sc oSA4) (a := aP (e)) (ss := sc (oR4 p)) (by unfold rej2Chk; vlayd))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide) (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by rw [h20.get .x0]; exact hr01
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.MatrixMask.mask_ok L20 (a := aP (e)) (N := 32) (by decide) (by decide) (by vlayd) (by vlayd) hr20) fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  have e2 : pa s2 (aP (e)) = pa s (aP (e)) := sc_pa hP2 _
  have e20 : pa s20 (aP (e)) = pa s2 (aP (e)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 2,∀ i < 256,coeffAt s3.mem (poly4 (pa s (aP (e))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (aP (e))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega_arith)
  have e3 : ∀ k,pa s3 (aP (e+k)) = poly4 (pa s (aP (e))) k := fun k => by rw [pa_poly4,sc_pa hP13]
  obtain ⟨q,hq,h1,h0⟩ := h.va.ok
  have hA : ∀ e' < e,polyAt s3.mem (pa s3 (aP e')) = polyAt s.mem (pa s (aP e')) := fun e' he' => L.keepPolyAt hP13 (by vlay)
  refine ⟨h.va.vz.keep hF hp hP13 (by vzchk hF),h.va.nok,by rw [L.keepBytes hP13 (by vlayd)]; exact h.va.rho,
    fun e' he' => ?_,q && ((s2.gpr .x0).setWidth 32 == 1),?_,fun hq' e' he' => ?_,fun hq' => ?_⟩
  · by_cases hlt : e' < e
    · exact L.keepRed hP13 (by vlay) (h.va.red e' hlt)
    · obtain ⟨k,rfl⟩ : ∃ k,e'=e+k := ⟨e'-e,by omega_arith⟩
      rw [e3]
      by_cases hret : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one hret (hco4 k (by omega_arith))).2 (hred hret k (by omega_arith))
      · exact (masked_zero hret (hco4 k (by omega_arith))).1
  · rw [k3.get .x24,e24,h24,hq,and_flag _ (Q := (s2.gpr .x0).setWidth 32 = 1)
      (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true,beq_iff_eq] at hq'
    by_cases hlt : e' < e
    · obtain ⟨b,hb⟩ := h1 hq'.1 e' hlt
      exact ⟨b,by rw [hb,hA e' hlt]⟩
    · obtain ⟨k,rfl⟩ : ∃ k,e'=e+k := ⟨e'-e,by omega_arith⟩
      rcases hout with ⟨_,hb⟩ | ⟨hret,_⟩
      · obtain ⟨b,hb⟩ := hb k (by omega_arith)
        exact ⟨b,by rw [e3,(masked_one hq'.2 (hco4 k (by omega_arith))).1,← vseed2_eq h (by omega_arith)]; exact hb⟩
      · rw [hq'.2] at hret; exact absurd hret (by decide)
  · cases hqq : q
    · obtain ⟨e',he',hn⟩ := h0 hqq; exact ⟨e',by omega_arith,hn⟩
    · rw [hqq] at hq'
      simp only [Bool.true_and,beq_eq_false_iff_ne,ne_eq] at hq'
      rcases hout with ⟨hret,_⟩ | ⟨_,k,hk,hn⟩
      · exact absurd hret hq'
      · exact ⟨e+k,by omega_arith,by rw [← vseed2_eq h hk]; exact hn⟩



end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedSamplesBall`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)
open VG.Proof.MlDsa (coeffAt)

theorem vectorTail_taint : ∀j<80,
    (taint.check (Taint.ofRegs [.x28]) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (sc (oP j)) 256))
      (VG.Taint.hintOf taint (Taint.ofRegs [.x28]) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (sc 0) 256)))).isSome=true := by
  decide +kernel

theorem tail_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a : Ptr}
    (hw : inB wbs a 1024 = true) (hin : inB (rbs ++ wbs) a 1024 = true)
    (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1) :
    WP isa (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code a 256)) s fun s' => PPostB S s s' [(a, 1024)] ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 ∧
      ∀ i < 256, coeffAt s'.mem (pa s a) i = if (s.gpr .x0).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  refine WP.seq (WP.mono (and24_ok s) fun s₁ ⟨o₁, e₁⟩ => ?_)
  have P₁ : PostB S s s₁ [] := postB_of_keep o₁.keep (by decide) (by rw [o₁.mem]; exact Frame.refl _ _)
  have L₁ := L.post P₁
  have x0 : s₁.gpr .x0 = s.gpr .x0 := o₁.get .x0
  rw [← x0] at hr
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.MatrixMask.mask_ok L₁ (N := 16) (by decide) (by decide) hw hin hr) fun s' ⟨P', k', hc⟩ => ⟨?_, by rw [k'.get .x24, e₁], ?_⟩
  · refine PostB.trans P₁ ?_ (fun _ h => absurd h List.not_mem_nil) fun _ h => h
    have e : ([(a, 1024)] : List (Ptr × Nat)).map (toR s₁) = [(a, 1024)].map (toR s) :=
      map_toR_post P₁ (fun w hw => by rw [List.mem_singleton.mp hw]; exact L.ptrBs hin)
    rw [← e]; exact P'
  · intro i hi
    rw [← P₁.pa (L.ptrBs hin), hc i hi, x0, o₁.mem]


variable {p : Params} {S : Nat} (hF : VFacts p)
include hF

theorem ballTail_vpiece : VPiece p S (VB1 p) (VB p) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (cP p) 256)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc).x28) (vectorTail_taint _ (by omega_using [hkl, hl, hk]))⟩
  have L := h.1.vz.vc.lay hF hp
  obtain ⟨hv, hred, hout⟩ := h
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L (a := cP p) (by vlayd) (by vlayd) hr01) fun s' ⟨hP', x', hco⟩ => ?_
  have hvz := hv.vz.keep hF hp hP' (by vzchk hF)
  have e' : pa s' (cP p) = pa s (cP p) := sc_pa hP' _
  obtain ⟨q, hq, h1, h0⟩ := hv.ok
  rw [hq] at x'
  refine ⟨hvz, hv.nok, fun e he => L.keepRed hP' (by vlayd) (hv.red e he), ?_, q && ((s.gpr .x0).setWidth 32 == 1), ?_, fun hq' => ⟨fun e he => ?_, ?_⟩,
    fun hq' => ?_⟩
  · rw [e']
    by_cases h1 : (s.gpr .x0).setWidth 32 = 1
    · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
    · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x', and_flag _ (Q := (s.gpr .x0).setWidth 32 = 1) (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    obtain ⟨b, hb⟩ := h1 hq'.1 e he
    exact ⟨b, by rw [hb, L.keepPolyAt hP' (by vlayd)]⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    rcases hout with ⟨_, b, hb⟩ | ⟨h0', _⟩
    · exact ⟨b, by rw [e', (Proof.MlDsa.KeyGen.masked_one hq'.2 hco).1]; exact hb⟩
    · rw [hq'.2] at h0'; exact absurd h0' (by decide)
  · cases hqq : q
    · exact .inl (h0 hqq)
    · rw [hqq] at hq'
      simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hq'
      rcases hout with ⟨h1'', _⟩ | ⟨_, hn⟩
      · exact absurd h1'' hq'
      · exact .inr hn


end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples

end

end


section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

/-- The final phase preserves public table addresses even though its semantic
postcondition no longer needs table contents. -/
theorem finish_rootPair {S : Nat} (h16 : 16≤S) (hS : S<2^64) {p : Params} (hF : VFacts p) :
    RelCT isa (RootPair p S (SCx p S p.ℓ true p.k))
      (.seq (shake256With keccak.callee (hIns p) [⟨.x28,oCT,p.ctildeLen⟩])
        (cmpAnd (sc oCT) (.x27,0) p.ctildeLen))
      (RootPair p S (VFin p)) := by
  have h := finish_vpiece (keccak:=keccak) h16 hS hF
  exact rootPair_progress h.ok (RelCT.mono h.tr (fun _ _ h=>h.1) (fun _ _ _=>trivial))

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedNttTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Verify.Optimized
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Call (Ptr)

theorem forward_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State}
    (hp : vPre p S σ) {a : Ptr} (hc : VC p σ s) (roots : Sign.StaticRoots S s)
    (hr : inB (vR p++vW p) a 1024=true) (hw : inB (vW p) a 1024=true)
    (red : Reduced s.mem (pa s a)) : NttCallReady a s := by
  have L := hc.lay hF hp
  exact ⟨L.nwp hr,roots.nttTableAt (L.inW hw),red,
    Covers.cons roots.forward.readable (L.cR hr),L.cW hw⟩

theorem nttZ_tr {p : Params} (hF : VFacts p) {S i : Nat} (hi : i<p.ℓ) :
    RelCT isa (RootPair p S (SCx p S i false 0)) (forward (zP p i))
      (RootPair p S (SCx p S (i+1) false 0)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs⟩=>
    WP.mono (nttZ_ok hF hp hi hs) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  unfold forward
  apply positiveNttAt_tr (S := S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx⟩,⟨h',A',c',q',hy⟩⟩,et⟩ := hh
  have H := vc_two hF hσ hτ pub hx.vc hy.vc
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hr : inB (vR p++vW p) (zP p i) 1024=true := by vlayd
  have hw : inB (vW p) (zP p i) 1024=true := by vlayd
  have red {σ s : State} {h A c q} (hs : SC p S σ h A c q i false 0 s) :
      Reduced s.mem (pa s (zP p i)) := by
    have hz:=hs.z i hi
    simp only [Stored,decide_eq_false_iff_not.mpr (Nat.lt_irrefl i),Bool.false_eq_true,↓reduceIte] at hz
    exact hz.1
  exact ⟨forward_ready hF hσ hx.vc hx.roots hr hw (red hx),
    forward_ready hF hτ hy.vc hy.roots hr hw (red hy),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.1⟩

theorem nttC_tr {p : Params} (hF : VFacts p) {S : Nat} :
    RelCT isa (RootPair p S (SCx p S p.ℓ false 0)) (forward (cP p))
      (RootPair p S (SCx p S p.ℓ true 0)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs⟩=>
    WP.mono (nttC_ok hF hp hs) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  unfold forward
  apply positiveNttAt_tr (S := S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx⟩,⟨h',A',c',q',hy⟩⟩,et⟩ := hh
  have H := vc_two hF hσ hτ pub hx.vc hy.vc
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hr : inB (vR p++vW p) (cP p) 1024=true := by vlayd
  have hw : inB (vW p) (cP p) 1024=true := by vlayd
  exact ⟨forward_ready hF hσ hx.vc hx.roots hr hw hx.c.1,
    forward_ready hF hτ hy.vc hy.roots hr hw hy.c.1,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.1⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedRowState.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized VG.Proof.MlDsa.Arith.Montgomery

abbrev RowData (p : Params) (σ : State) (A : Nat→Nat→Poly) (c : Poly) (r stage : Nat) (s : State) : Prop :=
  match stage with
  | 0 => W p σ A r s
  | 1 => W p σ A r s ∧ PolyIs s.mem (pa s (tmP p)) (rU p σ r)
  | 2 => W p σ A r s ∧ PosPolyIs s.mem (pa s (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)
  | 3 => W p σ A r s ∧ PolyIs s.mem (pa s (tm2P p))
      (montgomeryMultiplyNTT (ntt c) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r))
  | 4 => PolyIs s.mem (pa s (wP p)) (scale montgomeryRInv (Diff p σ A c r))
  | _ => PolyIs s.mem (pa s (wP p)) (Proof.MlDsa.Verify.wRow p (vPk p σ) (vSig p σ) A (ntt c) r)

abbrev RowI (p : Params) (S r stage : Nat) (σ s : State) : Prop :=
  ∃h A c q,SC p S σ h A c q p.ℓ true r s ∧ RowData p σ A c r stage s

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedPiece.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call

structure Piece (p : Params) (S : Nat) (I J : State → State → Prop) (c : Prog isa) : Prop where
  ok : ∀ σ s, vPre p S σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (RootPair p S I) c fun _ _ => True

theorem Piece.of_vpiece {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (h : VPiece p S I J c) : Piece p S I J c :=
  ⟨h.ok, h.tr.mono (fun _ _ h=>h.1) (fun _ _ h=>h)⟩

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedSamplesTwoTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem vseeds2 {p : Params} {σ : State} {e : Nat} {s : State} (h : VS p σ e 2 s) :
    bytesAt s.mem (pa s (sc oSA4)) 68=seedOf p σ e++seedOf p σ (e+1) := by
  rw [show 68=34+34 from rfl,Proof.MlKem.bytesAt_add]
  have h0 := vseed2_eq h (k := 0) (by decide)
  have h1 := vseed2_eq h (k := 1) (by decide)
  simp only [Proof.MlDsa.seed4,Nat.mul_zero,Nat.add_zero,Nat.mul_one,
    VG.Proof.MlKem.AArch64.ptr_zero] at h0 h1
  rw [h0,h1]

theorem vcall2_piece {S : Nat} (hS : S<2^64) {cd : Prog isa} {nm : String}
    (C : CalleeOk S cd (VG.Proof.MlDsa.rejNTT2Contract AArch64.abi S)) {p : Params} (hF : VFacts p)
    {e : Nat} (he : e+2 ≤ p.k*p.ℓ) : VPiece p S (VS p · (e) 2) (VA p · (e+2))
      (.seq (callAt nm cd (rej2Args (sc oSA4) (aP e) (sc (oR4 p)))) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => vcall2_ok hS C hF hp he h,
    vrel_of (Q := fun x y => VTwo p S x y ∧ bytesAt x.mem (pa x (sc oSA4)) 68 = bytesAt y.mem (pa y (sc oSA4)) 68) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc,by
        rw [vseeds2 h,vseeds2 h']; simp only [seedOf,(vPub_eq hq).2.1]⟩)⟩
  have hc : rej2Chk (vR p) (vW p) (sc oSA4) (aP (e)) (sc (oR4 p)) = true := by unfold rej2Chk; vlayd
  have ok := fun x (L : Lay S (vR p) (vW p) x) => WP.mono (rej2At_ok hS C L (nm := nm) hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  have tail : RelCT isa (VTwo p S) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512)) fun _ _ => True := by
    refine RelCT.seq (VTwo.step (fun _ _ h => h) (block_nomem_tr fun i hi _ => by
      simp only [and24,List.mem_singleton] at hi; subst hi; rfl) ?_)
      (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (matrixMask_taint (e) (by omega) 512 (by simp)))
    have f := fun z => WP.mono (and24_ok z) fun z' ⟨o,_⟩ =>
      (⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩ : ∃ W,PostB S z z' W)
    exact fun x y _ => ⟨f x,f y⟩
  exact RelCT.seq (VTwo.step (fun _ _ h => h.1)
    (rej2At_tr (nm := nm) C (vOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) tail

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedSamples.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

private theorem twoCallee {S : Nat} (hS : S<2^64) :
    CalleeOk S VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
      (VG.Proof.MlDsa.rejNTT2Contract abi S) :=
  CalleeOk.of_verified hS VG.Proof.MlDsa.AArch64.Optimized.ResidentRej.two_verified
    (Nat.zero_le _) (by
      have hd : VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code.aarch64Depth=0 := by decide +kernel
      simp only [hd,Nat.mul_zero]; exact Nat.zero_le _) (by lit_decide)

theorem tail2_vpiece {S : Nat} (hS : S<2^64) {p : Params} (hF : VFacts p)
    (hmod : p.k*p.ℓ%4=2) :
    VPiece p S (VA p · (4*(p.k*p.ℓ/4))) (VA p · (4*(p.k*p.ℓ/4)+2))
      (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.tail2 p) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.tail2
  refine VPiece.seq (VPiece.mono
    (VPiece.seqR (I := fun j σ s=>VS p σ (4*(p.k*p.ℓ/4)) j s) 2 0
      (fun j _ hj=>vslot2_piece hF (by omega) (by omega)))
    (fun _ _ _ h=>⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩)
    (fun _ _ _ h=>by simpa using h)) (vcall2_piece hS (twoCallee hS) hF (by omega))

theorem expAll_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (VA p · 0) (VA p · (p.k*p.ℓ))
      (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expAll P p) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expAll
  have hB : VPiece p S (VA p · 0) (VA p · (4*(p.k*p.ℓ/4)))
      (seqR (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4 P p) 0 (p.k*p.ℓ/4)) := by
    simpa only [Nat.zero_add,Nat.mul_zero] using
      (VPiece.seqR (I := fun g σ s=>VA p σ (4*g) s) (p.k*p.ℓ/4) 0
        (fun g _ hg=>expA4_vpiece hP hF (by omega)))
  split
  · rename_i he
    refine VPiece.mono (VPiece.seq hB (tail2_vpiece hP.s64 hF he))
      (fun _ _ _ h=>h) (fun _ _ _ h=>?_)
    have eq : 4*(p.k*p.ℓ/4)+2=p.k*p.ℓ := by omega
    simpa only [eq] using h
  · refine VPiece.mono (VPiece.seq hB
      (VPiece.seqR (I := fun e σ s=>VA p σ e s) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
        (fun e _ he=>expA_vpiece hP hF (by omega)))) (fun _ _ _ h=>h) (fun _ _ _ h=>?_)
    have eq : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4=p.k*p.ℓ := by omega
    simpa only [eq] using h

theorem samples_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (fun σ s=>Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) (VB p)
      (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples
  exact (copyRho_vpiece hF).seq ((expAll_vpiece hP hF).seq
    ((ballCall_vpiece hP hF).seq (ballTail_vpiece hF)))

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedSamplesRoots.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots)
open VG.Proof.MlDsa.AArch64.Verify.Optimized (RootPair rootPair_progress)

/-- A bounded phase retains the immutable transform roots without making
any sampled coefficients or SHAKE states public. -/
theorem rooted_piece {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (h : VPiece p S I J c) (hd : 16*c.aarch64Depth≤S) (hS : S<2^64) :
    VPiece p S (fun σ s=>I σ s ∧ StaticRoots S s) (fun σ s=>J σ s ∧ StaticRoots S s) c := by
  refine ⟨fun σ s hp hs=>hs.2.phase hd hS (h.ok σ s hp hs.1),?_⟩
  exact RelCT.mono h.tr
    (fun _ _ ⟨σ,τ,hσ,hτ,pub,ix,iy⟩=>⟨σ,τ,hσ,hτ,pub,ix.1,iy.1⟩)
    (fun _ _ _=>trivial)

/-- Sampling preserves both root tables while retaining the existing exact
success/failure and rejection-transcript semantics. -/
theorem samples_rooted_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S)
    {p : Params} (hF : VFacts p) :
    VPiece p S
      (fun σ s=>(Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) ∧ StaticRoots S s)
      (fun σ s=>VB p σ s ∧ StaticRoots S s)
      (Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p) :=
  rooted_piece (samples_vpiece hP hF) (samples_depth hP p) hP.s64

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedVectors.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.KeyGen

theorem vb_sc {p : Params} {S : Nat} {σ s : State} (h : VB p σ s) (ht : Sign.StaticRoots S s) :
    SCx p S 0 false 0 σ s := by
  obtain ⟨hh,A,c,q,hs⟩:=Verify.vb_sc h
  refine ⟨hh,A,c,q,hs.vc,ht,hs.hh,hs.hint,hs.nok,hs.gd,hs.a,?_,hs.c,hs.rows,hs.x24⟩
  intro i hi
  simpa only [Stored,Nat.not_lt_zero,decide_false,Bool.false_eq_true,↓reduceIte] using hs.z i hi

theorem nttZ_vector_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    (hs : SCx p S 0 false 0 σ s) :
    WP isa (seqR (fun i=>Impl.MlDsa.AArch64.Verify.Optimized.forward (zP p i)) 0 p.ℓ) s
      (SCx p S p.ℓ false 0 σ) := by
  simpa only [Nat.zero_add] using seqR_ok (I:=fun i=>SCx p S i false 0 σ) p.ℓ 0
    (fun i _ hi s ⟨h,A,c,q,hs⟩=>WP.mono (nttZ_ok hF hp (by omega) hs)
      fun t ht=>⟨h,A,c,q,ht⟩) s hs

theorem nttZ_vector_tr {p : Params} (hF : VFacts p) {S : Nat} :
    RelCT isa (RootPair p S (SCx p S 0 false 0))
      (seqR (fun i=>Impl.MlDsa.AArch64.Verify.Optimized.forward (zP p i)) 0 p.ℓ)
      (RootPair p S (SCx p S p.ℓ false 0)) := by
  simpa only [Nat.zero_add] using seqR_tr (Q:=fun i=>RootPair p S (SCx p S i false 0)) p.ℓ 0 fun i _ hi=>nttZ_tr hF (by omega)

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/InverseSingleCallTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

theorem inverseSingleAt_tr {S : Nat} {nm : String} {f : Ptr}
    (hf : (Arg.ptr f).Ok) {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → InverseSingleReady f x ∧ InverseSingleReady f y ∧
      pa x f=pa y f ∧ x.sp=y.sp ∧
      x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED") :
    RelCT isa Q (callAt nm staticCode (inverseSingleArgs f)) fun _ _=>True := by
  refine callAtSyms_tr (inverseSingle_callee S) (inverseSingleArgs_ok hf) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2=>?_
  obtain ⟨rx,ry,ef,esp,et⟩ := hQ x y hp
  refine ⟨[tableRegion (x.syms "VG_MLDSA_INV_FOLDED")],[outputRegion (pa x f)],
    inverseSingle_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ef,et]; exact inverseSingle_pre ry h2 hy2
  · change x1.callEntry.gpr .x0=y1.callEntry.gpr .x0 ∧ x1.sp=y1.sp ∧
      x1.syms "VG_MLDSA_INV_FOLDED"=y1.syms "VG_MLDSA_INV_FOLDED"
    rw [show x1.callEntry.gpr .x0=x1.gpr .x0 from rfl,show y1.callEntry.gpr .x0=y1.gpr .x0 from rfl,Args.r0 h1,Args.r0 h2,
      Args.sp h1,Args.sp h2,hy1,hy2]
    exact ⟨ef,esp,et⟩
  · rw [ef,et]; exact ry.readable
  · rw [ef]; exact ry.writable
end VG.Proof.MlDsa.AArch64.Optimized.Inverse
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedRowArithmeticTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized

theorem product_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 2)) (Impl.MlDsa.AArch64.Verify.Optimized.product p)
      (RootPair p S (RowI p S r 3)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw,ht⟩=>
    WP.mono (product_ok hF hp hr hs hw ht) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.product
  apply MontProduct.at_tr (S:=S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide)) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx,tx⟩,⟨h',A',c',q',hy,wy,ty⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨product_ready hF hσ hr hx wx tx,product_ready hF hτ hr hy wy ty,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.pa (show Reg.x28∈bases from by decide),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2⟩

theorem subtract_tr {p : Params} (hF : VFacts p) {S r : Nat} (hS : S<2^64) (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 3)) (Impl.MlDsa.AArch64.Verify.Optimized.subtract p)
      (RootPair p S (RowI p S r 4)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw,ht⟩=>
    WP.mono (subtract_ok hF hp hr hs hw ht) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : accChk (vR p) (vW p) (wP p) (tm2P p)=true := by unfold accChk;vlay
  have C : CalleeOk S (Impl.MlDsa.AArch64.Optimized.AddSub.code true) (subContract abi S) :=
    CalleeOk.of_verified hS AddSub.sub_verified (Nat.zero_le _) (by change 0≤S;omega) (by lit_decide)
  apply accAt_tr (op:=sub) C (vOk p) hc
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx,tx⟩,⟨h',A',c',q',hy,wy,ty⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨H.lx,H.ly,⟨wx.1,tx.1⟩,⟨wy.1,ty.1⟩,H.same⟩

theorem inverse_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 4)) (Impl.MlDsa.AArch64.Verify.Optimized.inverse (wP p))
      (RootPair p S (RowI p S r 5)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw⟩=>
    WP.mono (inverse_ok hF hp hr hs hw) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.inverse
  apply Inverse.inverseSingleAt_tr (S:=S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx⟩,⟨h',A',c',q',hy,wy⟩⟩,et⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨inverse_ready hF hσ hr hx wx,inverse_ready hF hτ hr hy wy,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.2⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedDotTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Verify (zHat dotAcc foldl_dot)

private theorem poly_addr (s : State) (b j : Nat) :
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (b+j)))=
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP b))+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem dot_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) :
    MontDot.Ready p.ℓ (wP p) (aP (p.ℓ*r)) (zP p 0) s := by
  have L := hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hrow : p.ℓ*r+p.ℓ≤p.k*p.ℓ := by
    have hm:=Nat.mul_le_mul_left p.ℓ (show r+1≤p.k by omega)
    rw [Nat.mul_succ,Nat.mul_comm p.ℓ p.k] at hm
    exact hm
  have hn : p.ℓ=4∨p.ℓ=5∨p.ℓ=7 := by rcases hF.mem with rfl|rfl|rfl <;> decide
  have ro : inB (vR p++vW p) (wP p) 1024=true := by vlayd
  have ra : inB (vR p++vW p) (aP (p.ℓ*r)) (1024*p.ℓ)=true := by vlayd
  have rb : inB (vR p++vW p) (zP p 0) (1024*p.ℓ)=true := by vlayd
  have wo : inB (vW p) (wP p) 1024=true := by vlayd
  have hA j (hj : j<p.ℓ) : PolyIs s.mem (pa s (aP (p.ℓ*r))+BitVec.ofNat 64 (1024*j)) (A' r j) := by
    have hv:=hs.a r hr j hj
    change PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.ℓ*r+j)))) _ at hv
    rwa [poly_addr] at hv
  have hB j (hj : j<p.ℓ) : PosPolyIs s.mem (pa s (zP p 0)+BitVec.ofNat 64 (1024*j)) (zHat p (vSig p σ) j) := by
    have hv:=hs.z j hj
    simp only [Stored,decide_eq_true_eq.mpr hj,↓reduceIte,ite_eq_left hj] at hv
    change PosPolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k*p.ℓ+(1+p.k+j))))) _ at hv
    have he : p.k*p.ℓ+(1+p.k+j)=(p.k*p.ℓ+(1+p.k))+j := by omega
    rw [he,poly_addr] at hv
    simpa only [zP,vP,Nat.add_zero] using hv
  have ready : MontDot.Ready p.ℓ (wP p) (aP (p.ℓ*r)) (zP p 0) s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.disj (by vlayd),L.disj (by vlayd),
      fun j hj=>(PosPolyIs.of_canonical (hA j hj)).bound,fun j hj=>(hB j hj).bound,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  exact ready

theorem dot_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (SCx p S p.ℓ true r))
      (Impl.MlDsa.AArch64.Verify.Optimized.dot p r)
      (RootPair p S fun σ s=>∃h A c q,SC p S σ h A c q p.ℓ true r s ∧ W p σ A r s) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs⟩=>
    WP.mono (dot_ok hF hp hr hs) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  have hn : p.ℓ=4∨p.ℓ=5∨p.ℓ=7 := by rcases hF.mem with rfl|rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Verify.Optimized.dot
  apply MontDot.at_tr (S:=S) hn (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide)) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx⟩,⟨h',A',c',q',hy⟩⟩,_⟩ := hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨dot_ready hF hσ hr hx,dot_ready hF hτ hr hy,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.pa (show Reg.x28∈bases from by decide),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedRowStartTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized

theorem unpack_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 0)) (unpackT1At P (.x25,32+320*r) (tmP p))
      (RootPair p S (RowI p S r 1)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw⟩=>
    WP.mono (unpack_ok hP hF hp hr hs hw) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr;have hpk:=hF.pk
  have hc : rwChk (vR p) (vW p) (.x25,32+320*r) 320 (tmP p) 1024=true := by unfold rwChk;vlay
  apply t1At_tr hP.unpackT1 (vOk p) hc
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,_⟩,⟨h',A',c',q',hy,_⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨H.lx,H.ly,H.same⟩

theorem nttT_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 1)) (Impl.MlDsa.AArch64.Verify.Optimized.forward (tmP p))
      (RootPair p S (RowI p S r 2)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw,ht⟩=>
    WP.mono (nttT_ok hF hp hr hs hw ht) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.forward
  apply positiveNttAt_tr (S:=S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,_,tx⟩,⟨h',A',c',q',hy,_,ty⟩⟩,et⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have rd : inB (vR p++vW p) (tmP p) 1024=true := by vlayd
  have wr : inB (vW p) (tmP p) 1024=true := by vlayd
  exact ⟨forward_ready hF hσ hx.vc hx.roots rd wr tx.1,
    forward_ready hF hτ hy.vc hy.roots rd wr ty.1,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.1⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedRowTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized

theorem hintPack_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 5)) (Impl.MlDsa.AArch64.Verify.Optimized.hintPack p r)
      (RootPair p S (SCx p S p.ℓ true (r+1))) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw⟩=>
    WP.mono (hintPack_ok hF hp hr hs hw) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.hintPack
  apply UseHintPack.at_tr (S:=S) (Round.isG_of_mem hF.g2.1)
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide)) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx⟩,⟨h',A',c',q',hy,wy⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨hintPack_ready hF hσ hr hx wx,hintPack_ready hF hτ hr hy wy,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.pa (show Reg.x28∈bases from by decide),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2⟩

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedBody.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.KeyGen (ifn)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem hint_depth {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) :
    16*(hint P p).aarch64Depth≤S := by
  have hh : DLe (S/16) P.hintUnpack := ⟨by have := hP.hintUnpack.fd; omega, hP.hintUnpack.nd⟩
  have hd : DLe (S/16) (hint P p) := by unfold hint;dle_tac
  have := hd.le;omega

theorem hint_noDit {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params)  :
    (hint P p).all (fun i => !i.touchesDit) = true := by
  have hh : DLe (S/16) P.hintUnpack := ⟨by have := hP.hintUnpack.fd; omega, hP.hintUnpack.nd⟩
  have hd : DLe (S/16) (hint P p) := by unfold hint;dle_tac
  exact hd.nd

theorem zOne_depth {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) (i : Nat) :
    16*(zOne P p i).aarch64Depth≤S := by
  have hb : DLe (S/16) P.bitUnpack := ⟨by have := hP.bitUnpack.fd; omega, hP.bitUnpack.nd⟩
  have hn : DLe (S/16) P.normLt := ⟨by have := hP.normLt.fd; omega, hP.normLt.nd⟩
  have hd : DLe (S/16) (zOne P p i) := by unfold zOne;dle_tac
  have := hd.le;omega

theorem zOne_noDit {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) (i : Nat)  :
    (zOne P p i).all (fun i => !i.touchesDit) = true := by
  have hb : DLe (S/16) P.bitUnpack := ⟨by have := hP.bitUnpack.fd; omega, hP.bitUnpack.nd⟩
  have hn : DLe (S/16) P.normLt := ⟨by have := hP.normLt.fd; omega, hP.normLt.nd⟩
  have hd : DLe (S/16) (zOne P p i) := by unfold zOne;dle_tac
  exact hd.nd

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

/-! # Shared prepared-key verification proof composition -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized

def CachedVRel (p : Params) (S : Nat) (I : State → State → Prop) (x y : State) : Prop :=
  Verify.Optimized.RootPair p S
    (fun σ s => I σ s ∧ (s.gpr .x22 ≠ 0 → PublicCache p S σ s)) x y ∧
    SameIn [.x21, .x22] x y

theorem cached_v_progress {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hw : ∀ σ s, vPre p S σ → I σ s → (s.gpr .x22 ≠ 0 → PublicCache p S σ s) →
      WP isa code s fun t => J σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t))
    (ht : RelCT isa (CachedVRel p S I) code fun _ _ => True) :
    RelCT isa (CachedVRel p S I) code (CachedVRel p S J) := by
  intro x y tx ty u v h ex ey
  have trace := (ht _ _ _ _ _ _ h ex ey).1
  obtain ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩ := h
  obtain ⟨_, u', eu, hu⟩ := hw σ x ps hx.1 hx.2
  obtain ⟨_, v', ev, hv⟩ := hw τ y pt hy.1 hy.2
  obtain ⟨_, rfl⟩ := Exec.det ex eu
  obtain ⟨_, rfl⟩ := Exec.det ey ev
  refine ⟨trace, ⟨⟨σ, τ, ps, pt, pub, hu, hv⟩, ?_⟩, ?_⟩
  · simpa only [VG.Proof.MlDsa.AArch64.Sign.RootSymbolsEq,
      VG.AArch64.Exec.syms ex, VG.AArch64.Exec.syms ey] using roots
  · refine ⟨fun r hr => ?_, by rw [(hj _ _ hu.1).sp, (hj _ _ hv.1).sp,
      ← (hi _ _ hx.1).sp, ← (hi _ _ hy.1).sp, hm.2]⟩
    have hk : r ∈ VG.Proof.MlDsa.AArch64.KeyGen.untouched := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [(hj _ _ hu.1).cs r hk, (hj _ _ hv.1).cs r hk,
      ← (hi _ _ hx.1).cs r hk, ← (hi _ _ hy.1).cs r hk, hm.1 r hr]

theorem cached_v_lift {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hw : ∀ σ s, vPre p S σ → I σ s → WP isa code s (J σ))
    (ht : RelCT isa (Verify.Optimized.RootPair p S I) code fun _ _ => True)
    (hd : 16 * code.aarch64Depth ≤ S) (hS : S < 2 ^ 64) :
    RelCT isa (CachedVRel p S I) code (CachedVRel p S J) := by
  apply cached_v_progress hi hj
  · intro σ s hp hs hc
    exact WP.optionalCache (hw σ s hp hs) hc hd hS
      (fun t ht => ((hj _ _ ht).cs .x21 (by decide)).trans ((hi _ _ hs).cs .x21 (by decide)).symm)
      (fun t ht => ((hj _ _ ht).cs .x22 (by decide)).trans ((hi _ _ hs).cs .x22 (by decide)).symm)
  · refine RelCT.mono ht ?_ (fun _ _ h => h)
    rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, _⟩
    exact ⟨⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩, roots⟩

theorem optimized_row_top {p : Params} {S r stage : Nat} {σ s : State}
    (h : Verify.Optimized.RowI p S r stage σ s) : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s := by
  obtain ⟨_, _, _, _, h, _⟩ := h
  exact h.vc.top

theorem keyRow_optimized_tr
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r < p.k)
    (hd : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow P p r).aarch64Depth ≤ S) :
    RelCT isa (CachedVRel p S (Verify.Optimized.RowI p S r 0))
      (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow P p r)
      (CachedVRel p S (Verify.Optimized.RowI p S r 2)) := by
  refine cached_v_progress (fun _ _ h => optimized_row_top h) (fun _ _ h => optimized_row_top h) ?_ ?_
  · intro σ s hp hs cache
    obtain ⟨h, A, c0, q, state, hw⟩ := hs
    have main := WP.mono (keyRow_optimized hP hF hp hr state hw cache)
      fun t ht => (show Verify.Optimized.RowI p S r 2 σ t from ⟨h, A, c0, q, ht⟩)
    exact WP.optionalCache main cache hd hP.s64
      (fun t ht => ((optimized_row_top ht).cs .x21 (by decide)).trans (state.vc.top.cs .x21 (by decide)).symm)
      (fun t ht => ((optimized_row_top ht).cs .x22 (by decide)).trans (state.vc.top.cs .x22 (by decide)).symm)
  · unfold Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow
    refine RelCT.ite ?_ ?_ ?_
    · intro x y h
      change some (x.gpr .x22 != 0) = some (y.gpr .x22 != 0)
      rw [h.2.1 .x22 (by simp)]
    · apply RelCT.mono (copy_cache_tr _ _) ?_ (fun _ _ _ => trivial)
      rintro x y ⟨⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, _⟩, hm⟩, _⟩
      obtain ⟨_, _, _, _, ix, _⟩ := hx.1
      obtain ⟨_, _, _, _, iy, _⟩ := hy.1
      have layout := vc_two hF ps pt pub ix.vc iy.vc
      refine ⟨fun r hr => ?_, layout.same.2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hm.1 .x21 (by simp)
      · exact layout.same.1 .x28 (by decide)
    · have old := RelCT.seq (Verify.Optimized.unpack_tr hP hF hr) (Verify.Optimized.nttT_tr hF hr)
      apply RelCT.mono old ?_
        (fun _ _ _ => trivial)
      rintro x y ⟨⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, _⟩, _⟩
      exact ⟨⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩, roots⟩

theorem optimized_sc_top {p : Params} {S j r : Nat} {cn : Bool} {σ s : State}
    (h : Verify.Optimized.SCx p S j cn r σ s) : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s := by
  obtain ⟨_, _, _, _, h⟩ := h
  exact h.vc.top

theorem row_optimized_tr
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r < p.k)
    (hdot : 16 * (Impl.MlDsa.AArch64.Verify.Optimized.dot p r).aarch64Depth ≤ S)
    (hkey : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow P p r).aarch64Depth ≤ S)
    (hrow : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r).aarch64Depth ≤ S) :
    RelCT isa (CachedVRel p S (Verify.Optimized.SCx p S p.ℓ true r))
      (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r)
      (CachedVRel p S (Verify.Optimized.SCx p S p.ℓ true (r + 1))) := by
  refine cached_v_progress (fun _ _ h => optimized_sc_top h) (fun _ _ h => optimized_sc_top h) ?_ ?_
  · intro σ s hp hs cache
    obtain ⟨h, A, c0, q, state⟩ := hs
    exact WP.mono (row_optimized hP hF hp hr hdot hrow state cache)
      fun t ht => ⟨⟨h, A, c0, q, ht.1⟩, ht.2⟩
  · unfold Impl.MlDsa.AArch64.PreparedKey.Verify.row
    refine RelCT.seq (R := CachedVRel p S (Verify.Optimized.RowI p S r 0))
      (cached_v_lift (fun _ _ h => optimized_sc_top h) (fun _ _ h => optimized_row_top h)
        (fun σ s hp ⟨h, A, c0, q, state⟩ => WP.mono (Verify.Optimized.dot_ok hF hp hr state)
          fun _ ht => ⟨h, A, c0, q, ht⟩)
        (RelCT.mono (Verify.Optimized.dot_tr hF hr) (fun _ _ h => h) (fun _ _ _ => trivial))
        hdot hP.s64) ?_
    refine RelCT.seq (keyRow_optimized_tr hP hF hr hkey) ?_
    refine RelCT.mono (RelCT.seq (Verify.Optimized.product_tr hF hr)
      (RelCT.seq (Verify.Optimized.subtract_tr hF hP.s64 hr)
        (RelCT.seq (Verify.Optimized.inverse_tr hF hr) (Verify.Optimized.hintPack_tr hF hr))))
      ?_ (fun _ _ _ => trivial)
    rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, _⟩
    exact ⟨⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩, roots⟩

theorem forward_dle (a : Impl.MlDsa.AArch64.Call.Ptr) :
    Message.DLe 1 (Impl.MlDsa.AArch64.Verify.Optimized.forward a) := by
  have hp := Message.DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.positiveNtt_callee 16).fd
    (VG.Proof.MlDsa.AArch64.Optimized.positiveNtt_callee 16).nd
  unfold Impl.MlDsa.AArch64.Verify.Optimized.forward
  dle_tac

theorem keyRow_dle {P : Prims}
    (hP : PrimsOk P 16) (p : Params) (r : Nat) :
    Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow P p r) := by
  have hc : Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.copy (tmP p) (.x21, 1024 * r) 1024) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.copy
    split <;> dle_tac
  have hu := Message.DLe.of_fd hP.unpackT1.fd hP.unpackT1.nd
  have hf := forward_dle (tmP p)
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow
  dle_tac

theorem row_dle {P : Prims}
    (hP : PrimsOk P 16) (p : Params) (r : Nat) :
    Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r) := by
  have hk := keyRow_dle hP p r
  have hinv := Message.DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.Inverse.inverseSingle_callee 16).fd
    (VG.Proof.MlDsa.AArch64.Optimized.Inverse.inverseSingle_callee 16).nd
  have hdot : Message.DLe 1 (Impl.MlDsa.AArch64.Optimized.MontDot.dot p.ℓ) := by
    unfold Impl.MlDsa.AArch64.Optimized.MontDot.dot
    dle_tac
  have hprod : Message.DLe 1 Impl.MlDsa.AArch64.Optimized.MontProduct.code := by
    unfold Impl.MlDsa.AArch64.Optimized.MontProduct.code
    dle_tac
  have hminus : Message.DLe 1 (Impl.MlDsa.AArch64.Optimized.AddSub.code true) := by
    unfold Impl.MlDsa.AArch64.Optimized.AddSub.code
    dle_tac
  have hpack : Message.DLe 1 Impl.MlDsa.AArch64.Optimized.UseHintPack.prog := by
    unfold Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
      Impl.MlDsa.AArch64.Round.zext Impl.MlDsa.AArch64.Round.onGamma
      Impl.MlDsa.AArch64.Optimized.UseHintPack.code
    dle_tac
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.row
  dle_tac

structure CachePiece (p : Params) (S : Nat) (I J : State → State → Prop) (code : Prog isa) : Prop where
  ok : ∀ σ s, vPre p S σ → I σ s → (s.gpr .x22 ≠ 0 → PublicCache p S σ s) →
    WP isa code s fun t => J σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t)
  tr : RelCT isa (CachedVRel p S I) code (CachedVRel p S J)

theorem CachePiece.seq {p : Params} {S : Nat} {I J K : State → State → Prop} {a b : Prog isa}
    (ha : CachePiece p S I J a) (hb : CachePiece p S J K b) : CachePiece p S I K (.seq a b) :=
  ⟨fun σ s hp hs hc => WP.seq (WP.mono (ha.ok σ s hp hs hc)
    fun t ht => hb.ok σ t hp ht.1 ht.2), RelCT.seq ha.tr hb.tr⟩

theorem CachePiece.of_old {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hw : ∀ σ s, vPre p S σ → I σ s → WP isa code s (J σ))
    (ht : RelCT isa (Verify.Optimized.RootPair p S I) code fun _ _ => True)
    (hd : 16 * code.aarch64Depth ≤ S) (hS : S < 2 ^ 64) : CachePiece p S I J code :=
  ⟨fun σ s hp hs hc => WP.optionalCache (hw σ s hp hs) hc hd hS
    (fun t ht => ((hj _ _ ht).cs .x21 (by decide)).trans ((hi _ _ hs).cs .x21 (by decide)).symm)
    (fun t ht => ((hj _ _ ht).cs .x22 (by decide)).trans ((hi _ _ hs).cs .x22 (by decide)).symm),
    cached_v_lift hi hj hw ht hd hS⟩

theorem CachePiece.mono {p : Params} {S : Nat} {I J I' J' : State → State → Prop} {code : Prog isa}
    (h : CachePiece p S I J code)
    (hi : ∀ σ s, I' σ s → I σ s) (hj : ∀ σ s, J σ s → J' σ s) : CachePiece p S I' J' code := by
  refine ⟨fun σ s hp hs hc => WP.mono (h.ok σ s hp (hi σ s hs) hc)
    (fun t ht => ⟨hj σ t ht.1, ht.2⟩), RelCT.mono h.tr ?_ ?_⟩
  · rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩
    exact ⟨⟨⟨σ, τ, ps, pt, pub, ⟨hi _ _ hx.1, hx.2⟩, ⟨hi _ _ hy.1, hy.2⟩⟩, roots⟩, hm⟩
  · rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩
    exact ⟨⟨⟨σ, τ, ps, pt, pub, ⟨hj _ _ hx.1, hx.2⟩, ⟨hj _ _ hy.1, hy.2⟩⟩, roots⟩, hm⟩

theorem CachePiece.seqR {p : Params} {S : Nat} {f : Nat → Prog isa}
    {I : Nat → State → State → Prop} :
    ∀ n a, (∀ k, a ≤ k → k < a + n → CachePiece p S (I k) (I (k + 1)) (f k)) →
      CachePiece p S (I a) (I (a + n)) (Impl.MlDsa.AArch64.Call.seqR f a n)
  | 0, a, _ => by
    simp only [Impl.MlDsa.AArch64.Call.seqR, Nat.add_zero]
    exact ⟨fun _ _ _ hs hc => WP.block_nil ⟨hs, hc⟩, RelCT.block_nil (fun _ _ h => h)⟩
  | n + 1, a, h => by
    have tail := CachePiece.seqR n (a + 1) (fun k h1 h2 => h k (by omega) (by omega))
    rw [show a + 1 + n = a + (n + 1) by omega] at tail
    exact (h a (Nat.le_refl _) (by omega)).seq tail

theorem dle_first {a b : Prog isa} (h : Message.DLe 1 (.seq a b)) : Message.DLe 1 a :=
  ⟨(Nat.max_le.mp h.le).1, by have := h.nd; simp only [Code.all, Bool.and_eq_true] at this; exact this.1⟩

theorem depth16 {code : Prog isa} (h : Message.DLe 1 code) : 16 * code.aarch64Depth ≤ 16 := by
  simpa using Nat.mul_le_mul_left 16 h.le

theorem finish_dle (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    Message.DLe 1 (.seq (shake256With v.callee (hIns p) [⟨.x28, oCT, p.ctildeLen⟩])
      (cmpAnd (Impl.MlDsa.AArch64.Call.sc oCT) (.x27, 0) p.ctildeLen)) := by
  obtain ⟨ha, hp, hs⟩ := Message.keccak_dle v
  dle_tac

theorem compute_optimized_piece (v : Proof.Sha3.AArch64.Permutation)
    {P : Prims} (hP : PrimsOk P 16) {p : Params} (hF : VFacts p) :
    CachePiece p 16 (fun σ s => VB p σ s ∧ Sign.StaticRoots 16 s) (VFin p)
      (Impl.MlDsa.AArch64.PreparedKey.Verify.compute v.callee P p) := by
  have hf := forward_dle
  have hvec := Message.DLe.seqR (fun i => hf (zP p i)) 0 p.ℓ
  have hdot (r : Nat) : Message.DLe 1 (Impl.MlDsa.AArch64.Verify.Optimized.dot p r) := by
    have h := row_dle hP p r
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.row at h
    exact dle_first h
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.compute
  refine CachePiece.seq (J := Verify.Optimized.SCx p 16 p.ℓ false 0) ?_
    (CachePiece.seq (J := Verify.Optimized.SCx p 16 p.ℓ true 0) ?_
      (CachePiece.seq (J := Verify.Optimized.SCx p 16 p.ℓ true p.k) ?_ ?_))
  · apply CachePiece.of_old (fun _ _ h => h.1.vz.vc.top) (fun _ _ h => optimized_sc_top h)
      (fun σ s hp hs => Verify.Optimized.nttZ_vector_ok hF hp (Verify.Optimized.vb_sc hs.1 hs.2))
      ?_ (depth16 hvec) (by decide)
    exact RelCT.mono (Verify.Optimized.nttZ_vector_tr hF)
      (fun _ _ ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩ =>
        ⟨⟨σ, τ, ps, pt, pub, Verify.Optimized.vb_sc hx.1 hx.2,
          Verify.Optimized.vb_sc hy.1 hy.2⟩, roots⟩) (fun _ _ _ => trivial)
  · apply CachePiece.of_old (fun _ _ h => optimized_sc_top h) (fun _ _ h => optimized_sc_top h)
      (fun σ s hp ⟨h, A, c0, q, state⟩ => WP.mono (Verify.Optimized.nttC_ok hF hp state)
        fun t ht => ⟨h, A, c0, q, ht⟩)
      (RelCT.mono (Verify.Optimized.nttC_tr hF) (fun _ _ h => h) (fun _ _ _ => trivial))
      (depth16 (hf (cP p))) (by decide)
  · simpa only [Nat.zero_add] using CachePiece.seqR (I := fun r => Verify.Optimized.SCx p 16 p.ℓ true r)
      p.k 0 (fun r _ hr => (show CachePiece p 16
        (Verify.Optimized.SCx p 16 p.ℓ true r) (Verify.Optimized.SCx p 16 p.ℓ true (r + 1))
        (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r) from
        ⟨fun σ s hp ⟨h, A, c0, q, state⟩ cache => WP.mono
          (row_optimized hP hF hp (by omega) (depth16 (hdot r))
            (depth16 (row_dle hP p r)) state cache)
          (fun t ht => ⟨⟨h, A, c0, q, ht.1⟩, ht.2⟩),
          row_optimized_tr hP hF (by omega) (depth16 (hdot r))
            (depth16 (keyRow_dle hP p r)) (depth16 (row_dle hP p r))⟩))
  · exact CachePiece.of_old (fun _ _ h => optimized_sc_top h) (fun _ _ h => h.1.top)
      (Verify.Optimized.finish_vpiece (keccak := v) (by decide) (by decide) hF).ok
      (RelCT.mono (Verify.Optimized.finish_rootPair (keccak := v) (by decide) (by decide) hF)
        (fun _ _ h => h) (fun _ _ _ => trivial)) (depth16 (finish_dle v p)) (by decide)
theorem CachePiece.ifOk {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    {T : State → Prop} [DecidablePred T]
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hx : ∀ σ s, vPre p S σ → I σ s → s.gpr .x24 = if T σ then 1 else 0)
    (hT : ∀ σ τ, vPre p S σ → vPre p S τ → vPub p S σ τ → (T σ ↔ T τ))
    (ht : CachePiece p S (fun σ s => I σ s ∧ T σ) J code)
    (he : ∀ σ s, vPre p S σ → I σ s → ¬ T σ → J σ s) :
    CachePiece p S I J (Impl.MlDsa.AArch64.KeyGen.ifOk code) := by
  have ev (σ s : State) (hp : vPre p S σ) (hs : I σ s) :
      isa.eval (.nonzero .x .x24) s = some (decide (T σ)) := by
    change some (s.gpr .x24 != 0) = some (decide (T σ))
    rw [hx σ s hp hs]
    by_cases h : T σ <;> simp [h]
  have hw : ∀ σ s, vPre p S σ → I σ s → (s.gpr .x22 ≠ 0 → PublicCache p S σ s) →
      WP isa (Impl.MlDsa.AArch64.KeyGen.ifOk code) s fun t => J σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t) := by
    intro σ s hp hs hc
    unfold Impl.MlDsa.AArch64.KeyGen.ifOk
    exact WP.ite (decide (T σ)) (ev σ s hp hs)
      (fun hb => ht.ok σ s hp ⟨hs, of_decide_eq_true hb⟩ hc)
      (fun hb => WP.block_nil ⟨he σ s hp hs (of_decide_eq_false hb), hc⟩)
  refine ⟨hw, cached_v_progress hi hj hw ?_⟩
  unfold Impl.MlDsa.AArch64.KeyGen.ifOk
  refine RelCT.ite ?_ ?_ (RelCT.block_nil (fun _ _ _ => trivial))
  · rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩
    rw [ev σ x ps hx.1, ev τ y pt hy.1, decide_eq_decide.mpr (hT σ τ ps pt pub)]
  · refine RelCT.mono ht.tr ?_ (fun _ _ _ => trivial)
    rintro x y ⟨⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩, hflag⟩
    rw [ev σ x ps hx.1] at hflag
    have tx : T σ := of_decide_eq_true (Option.some.inj hflag)
    have ty : T τ := (hT σ τ ps pt pub).mp tx
    exact ⟨⟨⟨σ, τ, ps, pt, pub, ⟨⟨hx.1, tx⟩, hx.2⟩, ⟨⟨hy.1, ty⟩, hy.2⟩⟩, roots⟩, hm⟩

theorem CachePiece.of_piece {p : Params} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (h : Verify.Optimized.Piece p 16 I J code) (hd : 16 * code.aarch64Depth ≤ 16) :
    CachePiece p 16 I J code := CachePiece.of_old hi hj h.ok h.tr hd (by decide)

theorem samples_scalar_dle {P : Prims} (hP : PrimsOk P 16) (p : Params) :
    Message.DLe 1 (Impl.MlDsa.AArch64.Verify.samples P p) := by
  have hr := Message.DLe.of_fd hP.rejNtt.fd hP.rejNtt.nd
  have hr4 := Message.DLe.of_fd hP.rej4.fd hP.rej4.nd
  have hb := Message.DLe.of_fd hP.ball.fd hP.ball.nd
  unfold Impl.MlDsa.AArch64.Verify.samples
  dle_tac

/-- The samples of either kind, with the root tables kept. -/
theorem samples_piece (v : Proof.Sha3.AArch64.Permutation)
    {P : Prims} (hP : PrimsOk P 16) {p : Params} (hF : VFacts p) :
    CachePiece p 16 (fun σ s => (Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) ∧ Sign.StaticRoots 16 s)
      (fun σ s => VB p σ s ∧ Sign.StaticRoots 16 s)
      (if v.callee.pairedSha3 then Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p
        else Impl.MlDsa.AArch64.Verify.samples P p) := by
  split
  · exact CachePiece.of_piece (fun _ _ h => h.1.1.1.vc.top)
      (fun _ _ h => h.1.vz.vc.top) (Verify.Optimized.Piece.of_vpiece (OptimizedSamples.samples_rooted_vpiece hP hF))
      (OptimizedSamples.samples_depth hP p)
  · exact CachePiece.of_piece (fun _ _ h => h.1.1.1.vc.top)
      (fun _ _ h => h.1.vz.vc.top) (Verify.Optimized.Piece.of_vpiece
        (OptimizedSamples.rooted_piece (Verify.samples_vpiece hP hF) (depth16 (samples_scalar_dle hP p)) hP.s64))
      (depth16 (samples_scalar_dle hP p))

theorem body_piece (v : Proof.Sha3.AArch64.Permutation)
    {P : Prims} (hP : PrimsOk P 16) {p : Params} (hF : VFacts p) :
    CachePiece p 16 (fun σ s => (VC p σ s ∧ s.gpr .x24 = 1) ∧ Sign.StaticRoots 16 s)
      (VFin p) (Impl.MlDsa.AArch64.PreparedKey.Verify.body v.callee P p) := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.body
  refine CachePiece.seq (CachePiece.of_piece (fun _ _ h => h.1.1.top)
    (fun _ _ h => h.1.1.top) (Verify.Optimized.Piece.of_vpiece
      (OptimizedSamples.rooted_piece (Verify.hint_vpiece hP hF)
        (Verify.Optimized.hint_depth hP p) hP.s64)) (Verify.Optimized.hint_depth hP p))
    (CachePiece.ifOk (T := fun σ => (hintOf p σ).isSome = true)
      (fun _ _ h => h.1.1.top) (fun _ _ h => h.1.top) (fun _ _ _ h => h.1.2.1)
      (fun _ _ _ _ pub => by rw [hintOf, hintOf, (vPub_eq pub).2.2.2.1]) ?_ ?_)
  · refine CachePiece.seq (J := fun σ s => Z0 p p.ℓ σ s ∧ Sign.StaticRoots 16 s) ?_
      (CachePiece.ifOk (T := fun σ => normOk p σ p.ℓ)
        (fun _ _ h => h.1.1.vc.top) (fun _ _ h => h.1.top)
        (fun _ _ _ h => h.1.2)
        (fun _ _ _ _ pub => by simp only [normOk, zOf, (vPub_eq pub).2.2.2.1]) ?_ ?_)
    · refine CachePiece.mono (CachePiece.seqR
        (I := fun j σ s => Z0 p j σ s ∧ Sign.StaticRoots 16 s) p.ℓ 0
        (fun j _ hj => CachePiece.of_piece (fun _ _ h => h.1.1.vc.top)
          (fun _ _ h => h.1.1.vc.top) (Verify.Optimized.Piece.of_vpiece
            (OptimizedSamples.rooted_piece (Verify.zOne_vpiece hP hF (by omega))
              (Verify.Optimized.zOne_depth hP p j) hP.s64)) (Verify.Optimized.zOne_depth hP p j))) ?_ ?_
      · intro σ s ⟨⟨⟨hv, hx, hH⟩, roots⟩, ht⟩
        refine ⟨⟨⟨hv, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩, ?_⟩, roots⟩
        · obtain ⟨hh, e⟩ := Option.isSome_iff_exists.mp ht
          exact ⟨hh, e, hH hh e⟩
        · rw [hx]
          exact flag_congr (iff_of_true ht (Verify.normOk_zero p σ))
      · intro _ _ h; simpa only [Nat.zero_add] using h
    · refine CachePiece.mono ((samples_piece v hP hF).seq (compute_optimized_piece v hP hF)) ?_
        (fun _ _ h => h)
      intro _ _ ⟨⟨hz, roots⟩, hn⟩
      exact ⟨⟨hz, hn⟩, roots⟩
    · intro σ s _ ⟨h, _⟩ hn
      refine ⟨h.1.vc, .inr ⟨by rw [h.2]; exact VG.Proof.MlDsa.KeyGen.ifn hn _ _, ?_⟩⟩
      obtain ⟨hh, e, _⟩ := h.1.hint
      exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e
        (by rw [Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1]; exact hn)
  · intro σ s _ ⟨h, _⟩ hn
    refine ⟨h.1, .inr ⟨by rw [h.2.1]; exact VG.Proof.MlDsa.KeyGen.ifn hn _ _, ?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ (Option.not_isSome_iff_eq_none.mp hn)]
    nofun

public theorem verify_core_correct (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp3 : Sign.Ok3 p)
    (σ : State) (hpre : (verifyCoreK p).pre σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) σ tr t ∧
      abiPreserved σ t ∧ (verifyCoreK p).post σ t := by
  have hP := KeyGen.prims_okWith (keccak := v)
  have hF := vfacts hp3
  have hp := hpre.1
  have cache := hpre.2.2
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) σ
      fun t => abiPreserved σ t ∧ (verifyContract p abi 16).post σ t := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.core
    have pro := WP.optionalCache
      ((OptimizedSamples.rooted_piece (Verify.pro_vpiece hF) (by change 0 ≤ 16; decide) hP.s64).ok
        σ σ hp ⟨rfl, hpre.2.1⟩) cache (Nat.zero_le _) hP.s64
      (fun t ht => ht.1.1.top.cs .x21 (by decide))
      (fun t ht => ht.1.1.top.cs .x22 (by decide))
    refine WP.seq (WP.mono pro fun t ⟨ht, hc⟩ => ?_)
    refine WP.seq (WP.mono ((body_piece v hP hF).ok σ t hp ht hc)
      fun u hu => ?_)
    exact (Verify.epi_vpiece hF).ok σ u hp hu.1
  obtain ⟨tr, t, he, hp⟩ := main
  exact ⟨tr, t, he, hp⟩

def CoreRel (p : Params) (x y : State) : Prop :=
  (verifyCoreK p).pre x ∧ (verifyCoreK p).pre y ∧ (verifyCoreK p).pub x y

theorem same_cache_metadata {σ τ x y : State} (hx : VG.Proof.MlDsa.AArch64.KeyGen.Top σ x)
    (hy : VG.Proof.MlDsa.AArch64.KeyGen.Top τ y) (h : SameIn [.x21, .x22] σ τ) :
    SameIn [.x21, .x22] x y := by
  refine ⟨fun r hr => ?_, by rw [hx.sp, hy.sp, h.2]⟩
  have hk : r ∈ VG.Proof.MlDsa.AArch64.KeyGen.untouched := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  rw [hx.cs r hk, hy.cs r hk, h.1 r hr]

theorem pro_optimized_tr (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hF : VFacts p) :
    RelCT isa (CoreRel p) (.block pro)
      (CachedVRel p 16 (fun σ s => (VC p σ s ∧ s.gpr .x24 = 1) ∧ Sign.StaticRoots 16 s)) := by
  intro x y tx ty u w ⟨hx, hy, pub⟩ ex ey
  have hP := KeyGen.prims_okWith (keccak := v)
  have trace := ((Verify.pro_vpiece hF).tr _ _ _ _ _ _
    ⟨x, y, hx.1, hy.1, pub.1, rfl, rfl⟩ ex ey).1
  have wx := WP.optionalCache
    ((OptimizedSamples.rooted_piece (Verify.pro_vpiece hF) (by change 0 ≤ 16; decide) hP.s64).ok
      x x hx.1 ⟨rfl, hx.2.1⟩) hx.2.2 (Nat.zero_le _) hP.s64
    (fun t ht => ht.1.1.top.cs .x21 (by decide)) (fun t ht => ht.1.1.top.cs .x22 (by decide))
  have wy := WP.optionalCache
    ((OptimizedSamples.rooted_piece (Verify.pro_vpiece hF) (by change 0 ≤ 16; decide) hP.s64).ok
      y y hy.1 ⟨rfl, hy.2.1⟩) hy.2.2 (Nat.zero_le _) hP.s64
    (fun t ht => ht.1.1.top.cs .x21 (by decide)) (fun t ht => ht.1.1.top.cs .x22 (by decide))
  obtain ⟨_, u', eu, hu⟩ := wx
  obtain ⟨_, w', ew, hw⟩ := wy
  obtain ⟨_, rfl⟩ := Exec.det ex eu
  obtain ⟨_, rfl⟩ := Exec.det ey ew
  refine ⟨trace, ⟨⟨x, y, hx.1, hy.1, pub.1, hu, hw⟩, ?_⟩,
    same_cache_metadata hu.1.1.1.top hw.1.1.1.top pub.2.2⟩
  have symbols := pub.2.1
  simpa only [Sign.RootSymbolsEq, VG.AArch64.Exec.syms ex, VG.AArch64.Exec.syms ey] using symbols

public theorem verify_core_ct (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp3 : Sign.Ok3 p) :
    ConstantTime isa (verifyCoreK p).pre (verifyCoreK p).pub
      (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) := by
  have hP := KeyGen.prims_okWith (keccak := v)
  have hF := vfacts hp3
  have trace : RelCT isa (CoreRel p)
      (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) (fun _ _ => True) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.core
    refine RelCT.seq (pro_optimized_tr v hF)
      (RelCT.seq (body_piece v hP hF).tr ?_)
    refine RelCT.mono (Verify.epi_vpiece (S := 16) hF).tr ?_ (fun _ _ _ => trivial)
    rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, _⟩, _⟩
    exact ⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩
  intro x y tx ty u w hx hy pub ex ey
  exact (trace _ _ _ _ _ _ ⟨hx, hy, pub⟩ ex ey).1

public theorem verify_core_dle (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) := by
  have hP := KeyGen.prims_okWith (keccak := v)
  have hvec := Message.DLe.seqR (fun i => forward_dle (zP p i)) 0 p.ℓ
  have hforward := forward_dle (cP p)
  have hrows := Message.DLe.seqR (fun r => row_dle hP p r) 0 p.k
  have hfinish := finish_dle v p
  have hcomp : Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Verify.compute v.callee (primsWith v.callee) p) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.compute
    exact Message.DLe.seq hvec (Message.DLe.seq hforward (Message.DLe.seq hrows hfinish))
  have hhint := Message.DLe.of_fd (Verify.Optimized.hint_depth hP p) (Verify.Optimized.hint_noDit hP p)
  have hz := Message.DLe.seqR (fun i => Message.DLe.of_fd (Verify.Optimized.zOne_depth hP p i)
    (Verify.Optimized.zOne_noDit hP p i)) 0 p.ℓ
  have hsamples : Message.DLe 1 (if v.callee.pairedSha3 then
      Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples (primsWith v.callee) p
      else Impl.MlDsa.AArch64.Verify.samples (primsWith v.callee) p) := by
    split
    · exact Message.DLe.of_fd (OptimizedSamples.samples_depth hP p) (OptimizedSamples.samples_noDit hP p)
    · exact samples_scalar_dle hP p
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.core Impl.MlDsa.AArch64.PreparedKey.Verify.body
  dle_tac

end VG.Proof.MlDsa.AArch64.PreparedKey

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Verify.Optimized

/-- The ABI of verification: with the static root tables of its transforms. -/
def selectedAbi : Abi isa :=
  abi.withConsts Sign.signRootConsts

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected

end

end

/-! ### `MlDsa.AArch64.Sign.OptimizedPairedSelectedTiming`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem selectedPairedChecks_tr {p : Params} (hp : Ok3 p) :
    PairedChecksCT p 16 (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) := by
  intro t ht
  apply positivePairedChecks_tr hp (ksChk_ok hp) (by decide) (by decide)
  intro σ τ he hs ht'
  exact leq_prefixAgree (paramsOk hp) he ht hs ht'

end VG.Proof.MlDsa.AArch64.Sign

end

end

/-! ### `MlDsa.AArch64.Sign.PairedSignSat`, which only this module used -/

section

/-! ## From `PairedRootsPre.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedRoots_pre {p : Params} {S : Nat} {s : State} (hS : 0<S)
    (hk : (signK p S).pre s) (hr : StaticRoots S s) (rp : PairedRoots S s)
    (hrd : s.rd=[⟨s.gpr .x0,p.skLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,32⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]) :
    (signContractT p (abi.withConsts pairedSignRootConsts) S).pre s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  dsimp only [signK,scrLen] at hk
  rw [Nat.mul_comm 8 (scratchWords p)] at hk
  sig_split hk
  rename_i _ hw d1 d2 d3 d4 d5 d6 d7 k1 k2 k3 k4 k5 n1 n2 n3 n4 n5
  have hsp := hk
  sig_pre [signContractT,signSig,abi,argRegs,Abi.withConsts,pairedSignRootConsts_eq,
    nttConsts_eq,Inverse.inverseConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,PairedTable.expandedWords_length,stackBelow]
  refine ⟨hsp,?_,hr.forward.held,hr.inverse.held,rp.held,hr.forward.fit,hr.forward.writable,
    hr.forward.stack,hr.inverse.fit,hr.inverse.writable,hr.inverse.stack,rp.fit,rp.writable,rp.stack,hr.forward.aligned,hr.inverse.aligned,rp.aligned,?_,hw,
    d1,d2,d3,d4,d5,d6,d7,k1,k2,k3,k4,k5,n1,n2,n3,n4,n5⟩
  · rw [hrd]; rfl
  · rw [hrd]; rfl

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `PairedSignSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

def pairedSignSatWith (p : Params) (m : Mem) : State :=
  { signSat p with
    mem := m
    syms := fun name=>if name="VG_MLDSA_NTT_EXPANDED" then 1048576 else if name="VG_MLDSA_INV_FOLDED" then 1052480 else 1056384
    rd := (signSat p).rd++[⟨1048576,3904⟩,⟨1052480,3904⟩,⟨1056384,4096⟩] }

theorem pairedSignSatWith_pre (p : Params) (hp : Ok3 p) (m : Mem)
    (hf : ∀j<488,m.readW (1048576+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD j 0)
    (hi : ∀j<488,m.readW (1052480+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD j 0)
    (hr : ∀j<512,m.readW (1056384+BitVec.ofNat 64 (8*j)) 64=
      Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD j 0) :
    (signContractT p (abi.withConsts pairedSignRootConsts) signStack).pre (pairedSignSatWith p m) := by
  apply pairedRoots_pre (by decide)
  · rcases hp with rfl|rfl|rfl
    all_goals dsimp [signK,scrLen,pairedSignSatWith,signSat]
    all_goals refine ⟨List.subset_append_left _ _, ?_⟩
    all_goals sig_and_intros
    all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide
  · refine ⟨⟨hf,by dsimp [pairedSignSatWith]; decide,?_,?_,by dsimp [pairedSignSatWith,signSat]; exact Region.disjoint_of_sep (by decide),
        by rw [show (pairedSignSatWith p m).syms "VG_MLDSA_NTT_EXPANDED" = 1048576 from rfl]; decide⟩,
      ⟨hi,by dsimp [pairedSignSatWith]; decide,?_,?_,by dsimp [pairedSignSatWith,signSat]; exact Region.disjoint_of_sep (by decide),
        by rw [show (pairedSignSatWith p m).syms "VG_MLDSA_INV_FOLDED" = 1052480 from rfl]; decide⟩⟩
    · apply Covers.one
      exact ⟨⟨1048576,3904⟩,by simp [pairedSignSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [pairedSignSatWith,signSat]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide)
    · apply Covers.one
      exact ⟨⟨1052480,3904⟩,by simp [pairedSignSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [pairedSignSatWith,signSat]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide)
  · refine ⟨hr,by dsimp [pairedSignSatWith]; decide,?_,?_,by dsimp [pairedSignSatWith,signSat]; exact Region.disjoint_of_sep (by decide),
      by rw [show (pairedSignSatWith p m).syms "VG_MLDSA_INV_PAIR" = 1056384 from rfl]; decide⟩
    · apply Covers.one
      exact ⟨⟨1056384,4096⟩,by simp [pairedSignSatWith],Region.contains_self _ _⟩
    · rcases hp with rfl|rfl|rfl
      all_goals dsimp [pairedSignSatWith,signSat]
      all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      all_goals sig_and_intros
      all_goals first | rfl | exact Region.disjoint_of_sep (by decide)
  · rfl

private theorem joined_three (F I P : List (BitVec 64)) (hf : F.length=488) (hi : I.length=488)
    (hp : P.length=512) :
    (∀j<488,(constMem 1048576 (F++I++P)).readW (1048576+BitVec.ofNat 64 (8*j)) 64=F.getD j 0) ∧
    (∀j<488,(constMem 1048576 (F++I++P)).readW (1052480+BitVec.ofNat 64 (8*j)) 64=I.getD j 0) ∧
    (∀j<512,(constMem 1048576 (F++I++P)).readW (1056384+BitVec.ofNat 64 (8*j)) 64=P.getD j 0) := by
  have hl : (F++I++P).length=1488 := by simp only [List.length_append,hf,hi,hp]
  constructor
  · intro j hj
    rw [constMem_held _ _ (by rw [hl]; decide) j (by rw [hl]; omega_using [hj])]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [hf,hi]; omega_using [hj] : j<(F++I).length),
      List.getElem?_append_left (by omega_using [hf, hj] : j<F.length)]
  · constructor
    · intro j hj
      have ha : (1052480+BitVec.ofNat 64 (8*j) : Addr)=1048576+BitVec.ofNat 64 (8*(488+j)) := by
        rw [Nat.mul_add,BitVec.ofNat_add,← BitVec.add_assoc]; rfl
      rw [ha,constMem_held _ _ (by rw [hl]; decide) (488+j) (by rw [hl]; omega_using [hj])]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [hf,hi]; omega_using [hj] : 488+j<(F++I).length),
        List.getElem?_append_right (by omega_using [hf] : F.length≤488+j),hf,Nat.add_sub_cancel_left]
    · intro j hj
      have ha : (1056384+BitVec.ofNat 64 (8*j) : Addr)=1048576+BitVec.ofNat 64 (8*(976+j)) := by
        rw [Nat.mul_add,BitVec.ofNat_add,← BitVec.add_assoc]; rfl
      rw [ha,constMem_held _ _ (by rw [hl]; decide) (976+j) (by rw [hl]; omega_using [hj])]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp [hf,hi] : (F++I).length≤976+j),
        List.length_append,hf,hi,show 488+488=976 from rfl,Nat.add_sub_cancel_left]

def pairedSignSat (p : Params) : State := pairedSignSatWith p
  (constMem 1048576 (Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords++
    Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords++Impl.MlDsa.AArch64.Optimized.Paired.expandedWords))

theorem pairedSign_sat {p : Params} (hp : Ok3 p) :
    (signContractT p (abi.withConsts pairedSignRootConsts) signStack).pre (pairedSignSat p) := by
  obtain ⟨hf,hi,hr⟩ := joined_three _ _ _ TableConstants.staticNttWords_length
    InverseTable.expandedWords_length PairedTable.expandedWords_length
  exact pairedSignSatWith_pre p hp _ hf hi hr

end VG.Proof.MlDsa.AArch64.Sign

end

end

end


@[expose] public section


/-! ## SignCore -/
namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem selectedPairedSignLoop_tr (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) :
    RelCT isa (PairedRS p 16 (LeakEq p 0) (PositiveIK p 16))
      (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith v.callee (primsWith v.callee) p
        (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) (PositiveOX p 16) := by
  apply pairedSignLoop_tr (keccak:=v) (prims_okWith (keccak:=v)) hp (selectedPairedChecks_tr hp)
  · have hd := (Message.pairedCommit_dle v hp).le
    change 16 * _ ≤ 16
    omega_using [hd]
  · have hd := (Message.pairedBall_dle v p).le
    change 16 * _ ≤ 16
    omega_using [hd]

end VG.Proof.MlDsa.AArch64.Sign


namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Sign

def selectedExpansion (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) : Prog isa :=
  if v.callee.pairedSha3 && p.k != 4 then CachedMatrix.expandA (primsWith v.callee) p
  else expandA (primsWith v.callee) p

theorem selectedExpansion_depth (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) :
    16 * (selectedExpansion v p).aarch64Depth ≤ 16 := by
  unfold selectedExpansion
  split
  · exact CachedMatrix.expandA_depth (prims_okWith (keccak := v)) p
  · exact expandA_depth (prims_okWith (keccak := v)) p

theorem selectedExpansion_noDit (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) :
    (selectedExpansion v p).all (fun i => !i.touchesDit) = true := by
  unfold selectedExpansion
  split
  · exact CachedMatrix.expandA_noDit (prims_okWith (keccak := v)) p
  · exact expandA_noDit (prims_okWith (keccak := v)) p

theorem selectedExpansion_ok (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params}
    (hp : Ok3 p) (hc : aChk p = true) {σ s : State} (h : RootedSt p 16 σ s)
    (h1 : s.gpr .x24 = 1) :
    WP isa (selectedExpansion v p) s fun t => IA p 16 σ (p.k * p.ℓ) t ∧ StaticRoots 16 t := by
  unfold selectedExpansion
  split
  · exact CachedMatrix.rooted_expandA_ok (prims_okWith (keccak := v)) hp hc h h1
  · exact rooted_expandA_ok (prims_okWith (keccak := v)) hp hc h h1

theorem core_correct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    (σ : State) (hpre : (signK p 16).pre σ) (roots : StaticRoots 16 σ) (rp : PairedRoots 16 σ)
    (hcache : σ.gpr .x22 ≠ 0 → SecretCache p 16 σ σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p) σ tr t ∧
      abiPreserved σ t ∧ (signK p 16).post σ t := by
  have hc := allChk_ok hp
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hf⟩ := hc
  simp only [fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf
  obtain ⟨hsv, _⟩ := hf
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p) σ
      fun t => abiPreserved σ t ∧ ∃ u, FS p 16 σ u ∧ t.gpr .x0 = u.gpr .x24 ∧ t.mem = u.mem := by
    change WP isa (.seq (.block pro) (.seq (selectedExpansion v p)
      (.seq (ifOk (.seq (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee (primsWith v.callee) p)
        (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p))))) (.block epi)))) σ _
    refine WP.seq (WP.mono (WP.optionalCache
      (paired_prologue hp (by decide) hpre roots rp) hcache (Nat.zero_le _) (by decide)
      (fun t ht => ht.1.1.1.top.cs .x21 (by decide))
      (fun t ht => ht.1.1.1.top.cs .x22 (by decide)))
      fun s1 ⟨⟨⟨h1, hflag⟩, r1⟩, c1⟩ => ?_)
    refine WP.seq (WP.mono (WP.optionalCache (WP.pairedRoots
      (selectedExpansion_ok v hp ha h1 hflag) r1 (selectedExpansion_depth v p) (by decide))
      c1 (selectedExpansion_depth v p) (by decide)
      (fun t ht => (ht.1.1.st.top.cs .x21 (by decide)).trans (h1.1.top.cs .x21 (by decide)).symm)
      (fun t ht => (ht.1.1.st.top.cs .x22 (by decide)).trans (h1.1.top.cs .x22 (by decide)).symm))
      fun s2 ⟨⟨⟨h2, hr2⟩, r2⟩, c2⟩ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (.seq
      (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee (primsWith v.callee) p)
      (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p))))) s2 (FS p 16 σ) from ?_)
      fun s4 h4 => ?_)
    · unfold ifOk
      refine ifOkElse_ok (fun hn => ?_) fun hz => ?_
      · have hflag := x24_one h2.r01 hn
        obtain ⟨ok, fam⟩ := h2.ok hflag
        exact rest_ok v hp ⟨h2.st, ok, fam⟩ hr2 r2 c2
      · have hzero := x24_zero h2.r01 hz
        exact WP.block_nil ⟨h2.st, .inl hzero,
          fun hflag => absurd (hflag.symm.trans hzero) (by decide), fun _ => signMu_min_A (h2.bad hzero)⟩
    · exact WP.mono (epi_ok h4.st.top fun k hk => h4.st.lay.inR (hsv k hk))
        fun t ⟨habi, hret, hmem⟩ => ⟨habi, s4, h4, hret, hmem⟩
  obtain ⟨tr, t, he, habi, u, hu, hret, hmem⟩ := main
  refine ⟨tr, t, he, habi, ?_⟩
  have e23 : pa u (.x23, 0) = σ.gpr .x3 := by
    rw [pa, hu.st.top.regs (.x23, .x3) (by decide), BitVec.add_zero]
  show Outcome _ _ _
  rcases hu.r01 with h0 | h1
  · exact .inr ⟨by rw [hret, h0]; rfl, hu.bad h0⟩
  · exact .inl ⟨by rw [hret, h1]; rfl, maxBounds, by rw [hmem, ← e23]; exact hu.ok h1⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignCorrect -/
/-! ## SignCoreDepth -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Sign

theorem left_dle {d : Nat} {a b : Prog isa} (h : DLe d (.seq a b)) : DLe d a :=
  ⟨(Nat.max_le.mp h.le).1, by have := h.nd; simp only [Code.all, Bool.and_eq_true] at this; exact this.1⟩

theorem right_dle {d : Nat} {a b : Prog isa} (h : DLe d (.seq a b)) : DLe d b :=
  ⟨(Nat.max_le.mp h.le).2, by have := h.nd; simp only [Code.all, Bool.and_eq_true] at this; exact this.2⟩

theorem then_dle {d : Nat} {c : isa.Cond} {a b : Prog isa} (h : DLe d (.ite c a b)) : DLe d a :=
  ⟨(Nat.max_le.mp h.le).1, by have := h.nd; simp only [Code.all, Bool.and_eq_true] at this; exact this.1⟩

theorem selectedLoop_dle (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) :
    DLe 1 (selectedLoop v p) := by
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
    have h := cachedPairedSignWith_dle v hp'
    exact left_dle (right_dle (then_dle (left_dle (right_dle (right_dle h)))))
  · have h := pairedSignWith_dle v hp
    exact left_dle (right_dle (then_dle (left_dle (right_dle (right_dle h)))))

theorem core_dle (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) :
    DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p) := by
  have he : DLe 1 (selectedExpansion v p) := .of_fd (selectedExpansion_depth v p) (selectedExpansion_noDit v p)
  have hl := selectedLoop_dle v hp
  have hi := initialization_dle v p
  have old := pairedSignWith_dle v hp
  have hout := right_dle (right_dle (then_dle (left_dle (right_dle (right_dle old)))))
  change DLe 1 (.seq (.block pro) (.seq (selectedExpansion v p)
    (.seq (ifOk (.seq (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee (primsWith v.callee) p)
      (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p))))) (.block epi))))
  exact .seq (.block _ (by lit_decide)) (.seq he (.seq (.ite (.seq hi (.seq hl hout)) (.block _ rfl))
    (.block _ (by lit_decide))))

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignEntry -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

def signingMetadata (s : State) : State :=
  (s.write .x .x21 (s.gpr .x5)).write .x .x22 (s.gpr .x6)

theorem shared_sign_input {p : Params} (hp : Ok3 p) {s : State}
    (h : (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre s) :
    (signK p 48).pre s ∧ StaticRoots 48 s ∧ PairedRoots 48 s ∧
      (s.gpr .x6 ≠ 0 → SecretCache p 48 s (signingMetadata s)) := by
  sig_pre [signWithCacheContract, signWithCacheSig, signSig, abi, argRegs, Abi.withConsts,
    pairedSignRootConsts_eq, nttConsts_eq, Inverse.inverseConsts_eq,
    Abi.constRegions, Abi.constsHeld, TableConstants.staticNttWords_length,
    InverseTable.expandedWords_length, PairedTable.expandedWords_length, stackBelow] at h
  obtain ⟨hsp, hdrop, hf, hi, hpair, hff, hfw, hfs, hif, hiw, his, hpf, hpw, hps,
    hfa, hia, hpa, htake, hwr, d1, d2, d3, d4, d5, d6, d7, dc1, dc2,
    k1, k2, k3, k4, k5, kc, n1, n2, n3, n4, n5, _nc, hcache⟩ := h
  have hrd : s.rd = [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩,
      ⟨s.gpr .x5, (s.gpr .x6).toNat⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED", 3904⟩, ⟨s.syms "VG_MLDSA_INV_FOLDED", 3904⟩,
        ⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩] := by
    rw [← List.take_append_drop (s.rd.length - 3) s.rd, htake, hdrop]
  refine ⟨?_, ⟨⟨hf, hff, ?_, hfw, hfs, hfa⟩, ⟨hi, hif, ?_, hiw, his, hia⟩⟩,
    ⟨hpair, hpf, ?_, hpw, hps, hpa⟩, ?_⟩
  · have hsub : [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩] ⊆ s.rd := by
      intro R hR
      rw [hrd]
      exact List.mem_append_left _ (List.mem_append_left _ hR)
    dsimp only [signK, scrLen]
    rw [Nat.mul_comm 8 (scratchWords p)]
    exact ⟨hsub, hwr, d1, d2, d3, d4, d5, d6, d7, k1, k2, k3, k4, k5,
      n1, n2, n3, n4, n5, hsp⟩
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED", 3904⟩, ?_, Region.contains_self _ _⟩
    rw [hrd]
    simp
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_FOLDED", 3904⟩, ?_, Region.contains_self _ _⟩
    rw [hrd]
    simp
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩, ?_, Region.contains_self _ _⟩
    rw [hrd]
    simp
  · intro hne
    rcases hcache with hz | ⟨hlen, hvalues⟩
    · exact absurd hz hne
    change (s.gpr .x6).toNat = 1024 * (p.ℓ + 2 * p.k) at hlen
    have e21 : (signingMetadata s).gpr .x21 = s.gpr .x5 := by simp [signingMetadata, State.write]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rcases hp with rfl | rfl | rfl <;> decide
    · rw [e21, ← hlen]
      apply Covers.one
      refine ⟨⟨s.gpr .x5, (s.gpr .x6).toNat⟩, ?_, Region.contains_self _ _⟩
      change _ ∈ s.rd ++ s.wr
      rw [hrd]
      simp
    · intro R hR
      change R ∈ s.wr at hR
      rw [hwr] at hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rw [e21, ← hlen]
      rcases hR with rfl | rfl
      exacts [dc1.symm, dc2.symm]
    · rw [e21, ← hlen]
      exact kc.symm
    · intro i hii
      rw [pa, e21]
      exact hvalues i hii

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignFrames -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign

theorem cache_reframe {count S T : Nat} {f : Nat → Poly} {s t : State} {W : List Region}
    (h : ReadCache count S f s) (hf : Frame W s.mem t.mem)
    (hd : ∀ R ∈ W, (⟨s.gpr .x21, 1024 * count⟩ : Region).Disjoint R)
    (h21 : t.gpr .x21 = s.gpr .x21) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hst : Region.Sub (below t.sp T) (below s.sp S)) : ReadCache count T f t := by
  refine ⟨h.small, ?_, ?_, ?_, ?_⟩
  · simpa only [h21, hr, hw] using h.readable
  · simpa only [h21, hw] using h.writable
  · rw [h21]
    exact h.stack.sub_right hst
  · intro i hi
    simp only [pa, h21]
    exact VG.Proof.MlDsa.Verify.polyIs_frame hf
      (fun R hR => (hd R hR).sub_left (h.slice_sub hi)) (h.values i hi)

theorem staticTable_reframe {S T : Nat} {name : String} {words : List (BitVec 64)}
    {s t : State} {W : List Region} (h : StaticTable S name words s)
    (hf : Frame W s.mem t.mem) (hd : ∀ R ∈ W, (⟨s.syms name, 3904⟩ : Region).Disjoint R)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hy : t.syms = s.syms)
    (hst : Region.Sub (below t.sp T) (below s.sp S)) : StaticTable T name words t := by
  refine ⟨?_, by simpa only [hy] using h.fit, ?_, ?_, ?_, by simpa only [hy] using h.aligned⟩
  · intro i hi
    rw [hy, hf.readW (r := ⟨s.syms name, 3904⟩)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hd (by decide)]
    exact h.held i hi
  · simpa only [hy, hr, hw] using h.readable
  · simpa only [hy, hw] using h.writable
  · rw [hy]
    exact h.stack.sub_right hst

theorem pairedRoots_reframe {S T : Nat} {s t : State} {W : List Region} (h : PairedRoots S s)
    (hf : Frame W s.mem t.mem)
    (hd : ∀ R ∈ W, (⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩ : Region).Disjoint R)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hy : t.syms = s.syms)
    (hst : Region.Sub (below t.sp T) (below s.sp S)) : PairedRoots T t := by
  refine ⟨?_, by simpa only [hy] using h.fit, ?_, ?_, ?_, by simpa only [hy] using h.aligned⟩
  · intro i hi
    rw [hy, hf.readW (r := ⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hd (by decide)]
    exact h.held i hi
  · simpa only [hy, hr, hw] using h.readable
  · simpa only [hy, hw] using h.writable
  · rw [hy]
    exact h.stack.sub_right hst

def signInner (s : State) : State := pushState .x22 (pushState .x21 s)

theorem signInner_sp (s : State) : (signInner s).sp = s.sp - 32 := by
  simp only [signInner, pushState, BitVec.sub_sub]
  rfl

theorem signInner_frame (s : State) : Frame [below s.sp 32] s.mem (signInner s).mem := by
  have h1 : Frame [below s.sp 32] s.mem (pushState .x21 s).mem :=
    Frame.write (r := below s.sp 32) (Frame.refl _ _) (by simp) _
      (below_frame_contains s.sp 16 (by decide))
  refine Frame.write (r := below s.sp 32) h1 (by simp) _ ?_
  change (below s.sp 32).Contains ((s.sp - 16) - 16) 8
  rw [BitVec.sub_sub]
  change (below s.sp 32).Contains (s.sp - 32) 8
  simp [Region.Contains]

theorem metadata_setup (s : State) :
    WP isa (.block [.addImm .x .x21 .x5 0, .addImm .x .x22 .x6 0]) s fun t =>
      VG.Proof.MlKem.AArch64.Only [.x21, .x22] s t ∧
      t.gpr .x21 = s.gpr .x5 ∧ t.gpr .x22 = s.gpr .x6 := by
  open VG.Proof.MlKem.AArch64 in
  refine wp_addImm (by decide) fun u hu h21 => wp_addImm (by decide) fun t ht h22 => wp_nil ?_
  exact ⟨(hu.trans ht).mono (by simp), by rw [ht.get .x21, h21, BitVec.add_zero],
    by rw [h22, BitVec.add_zero, hu.get .x6]⟩

theorem sign_frame_guards {p : Params} {σ s : State} (pre : (signK p 48).pre σ)
    {offset : Nat} (ho : offset ≤ 32) (hw : s.wr = σ.wr)
    (hsp : s.sp = σ.sp - BitVec.ofNat 64 offset) :
    16 ≤ s.sp.toNat ∧ ∀ R ∈ s.wr, Region.Disjoint ⟨s.sp - 16, 16⟩ R := by
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, k4, k5, _, _, _, _, _, hstack⟩ := pre
  have hsub : Region.Sub (⟨s.sp - 16, 16⟩ : Region) (below σ.sp 48) := by
    have h1 := below_below σ.sp offset 16
    have h2 := below_sub (sp := σ.sp) (a := 16 + offset) (b := 48) (by omega_using [ho]) (by decide)
    rw [hsp]
    exact fun a ha => h2 a (h1 a ha)
  refine ⟨?_, ?_⟩
  · rw [hsp, toNat_sub_ofNat' (by omega_using [ho, hstack])]
    omega_using [ho, hstack]
  · intro R hR
    rw [hw, hwr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [k4.sub_left hsub, k5.sub_left hsub]

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignSetup -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign

theorem setup_sign_inputs {p : Params} (hp : Ok3 p) {σ s : State}
    (hpre : (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre σ)
    (hs : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signInner σ) s)
    (h21 : s.gpr .x21 = σ.gpr .x5) (h22 : s.gpr .x22 = σ.gpr .x6)
    (hy : s.syms = σ.syms) :
    (signK p 16).pre s ∧ StaticRoots 16 s ∧ PairedRoots 16 s ∧
      (s.gpr .x22 ≠ 0 → SecretCache p 16 s s) ∧
      skOf p s = skOf p σ ∧ muOf s = muOf σ ∧ rndOf s = rndOf σ ∧ s.gpr .x3 = σ.gpr .x3 := by
  obtain ⟨pre, roots, paired, cached⟩ := shared_sign_input hp hpre
  have e0 : s.gpr .x0 = σ.gpr .x0 := hs.get .x0
  have e1 : s.gpr .x1 = σ.gpr .x1 := hs.get .x1
  have e2 : s.gpr .x2 = σ.gpr .x2 := hs.get .x2
  have e3 : s.gpr .x3 = σ.gpr .x3 := hs.get .x3
  have e4 : s.gpr .x4 = σ.gpr .x4 := hs.get .x4
  have er : s.rd = σ.rd := hs.rd
  have ew : s.wr = σ.wr := hs.wr
  have esp : s.sp = σ.sp - 32 := hs.sp.trans (signInner_sp σ)
  have hframe : Frame [below σ.sp 32] σ.mem s.mem := by
    rw [hs.mem]
    exact signInner_frame σ
  have hsmall : Region.Sub (below σ.sp 32) (below σ.sp 48) := below_sub (by decide) (by decide)
  have hstack : Region.Sub (below s.sp 16) (below σ.sp 48) := by
    rw [esp]
    exact below_below σ.sp 32 16
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, k1, k2, k3, k4, k5,
    n1, n2, n3, n4, n5, hsp⟩ := pre
  have hkey : skOf p s = skOf p σ := by
    rw [skOf, skOf, e0]
    exact MlKem.bytesAt_frame hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact (k1.sub_left hsmall).symm) (by omega_using [n1])
  have hmu : muOf s = muOf σ := by
    rw [muOf, muOf, e1]
    exact MlKem.bytesAt_frame hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact (k2.sub_left hsmall).symm) (by decide)
  have hrnd : rndOf s = rndOf σ := by
    rw [rndOf, rndOf, e2]
    exact MlKem.bytesAt_frame hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact (k3.sub_left hsmall).symm) (by decide)
  refine ⟨?_, ?_, ?_, ?_, hkey, hmu, hrnd, e3⟩
  · dsimp only [signK]
    rw [er, ew, e0, e1, e2, e3, e4]
    refine ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7,
      k1.sub_left hstack, k2.sub_left hstack, k3.sub_left hstack,
      k4.sub_left hstack, k5.sub_left hstack, n1, n2, n3, n4, n5, ?_⟩
    rw [esp]
    change 16 ≤ (σ.sp - BitVec.ofNat 64 32).toNat
    rw [toNat_sub_ofNat' (by omega_using [hsp])]
    omega_using [hsp]
  · exact ⟨staticTable_reframe roots.forward hframe (fun R hR => by
        obtain rfl := List.mem_singleton.mp hR
        exact roots.forward.stack.sub_right hsmall) er ew hy hstack,
      staticTable_reframe roots.inverse hframe (fun R hR => by
        obtain rfl := List.mem_singleton.mp hR
        exact roots.inverse.stack.sub_right hsmall) er ew hy hstack⟩
  · exact pairedRoots_reframe paired hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact paired.stack.sub_right hsmall) er ew hy hstack
  · intro hn
    have hn' : σ.gpr .x6 ≠ 0 := by rwa [h22] at hn
    have hc := cached hn'
    have e21 : s.gpr .x21 = (signingMetadata σ).gpr .x21 := by
      simpa [signingMetadata, State.write] using h21
    have hc' : SecretCache p 16 σ s := cache_reframe hc hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact hc.stack.sub_right hsmall) e21 er ew hstack
    change ReadCache (p.ℓ + 2 * p.k) 16
      (fun i => (preparedSecretPolys p (skOf p s))[i]!) s
    rw [hkey]
    exact hc'

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignCorrect -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign

theorem common_frame_bounds {d : Nat} (hd : d ≤ 1) :
    16 * (d + 1) + 16 < 2 ^ 64 ∧ 16 * d + 16 < 2 ^ 64 := by omega_using [hd]

theorem withCache_correct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    (σ : State) (hpre : (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p) σ tr t ∧
      abiPreserved σ t ∧ (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).post σ t := by
  have pre := (shared_sign_input hp hpre).1
  have hd := common_frame_bounds (core_dle v hp).le
  have g0 := sign_frame_guards (s := σ) pre (offset := 0) (by decide) rfl (by simp)
  have g1 := sign_frame_guards (s := pushState .x21 σ) pre (offset := 16) (by decide) rfl rfl
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p) σ
      fun t => abiPreserved σ t ∧ (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).post σ t := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Sign.withCache
    refine WP.frameReg g0.1 g0.2 ?_ (by
      simpa only [Code.aarch64Depth, Instr.frameUnits, Nat.zero_max] using hd.1)
    refine WP.frameReg g1.1 g1.2 ?_ (by
      simpa only [Code.aarch64Depth, Nat.zero_max] using hd.2)
    refine WP.seq (WP.mono_syms (metadata_setup (signInner σ)) fun s ⟨hs, h21, h22⟩ hy => ?_)
    obtain ⟨hcore, roots, paired, cache, hkey, hmu, hrnd, e3⟩ :=
      setup_sign_inputs hp hpre hs h21 h22 hy
    obtain ⟨tr, t, he, habi, hpost⟩ := core_correct v hp s hcore roots paired cache
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
    · change Outcome (fun b => signMu p b (skOf p s) (muOf s) (rndOf s))
        ((t.gpr .x0).setWidth 32) (VG.Spec.Sha3.bytesAt t.mem (s.gpr .x3) p.sigLen) at hpost
      rw [hkey, hmu, hrnd, e3] at hpost
      sig_post [signWithCacheContract, signWithCacheSig, signSig, abi, argRegs, Abi.withConsts]
      simpa [skOf, muOf, rndOf, State.write] using hpost
  obtain ⟨tr, t, he, habi, hpost⟩ := main
  exact ⟨tr, t, he, habi, hpost⟩

end VG.Proof.MlDsa.AArch64.PreparedKey



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
      omega_using [hd]
    · have hd := (Message.pairedBall_dle v p).le
      change 16 * _ ≤ 16
      omega_using [hd]
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
      (lo := -(q : Int) + 1) (hi := (q : Int) - 1) (by omega_using []) (by omega_using [])
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
    omega_using [this]
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
      dsimp only [Sig.bufs, Sig.lists, Sig.alignedBufs, Elem.size]
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

theorem shared_verify_input {p : Params} (hp : Sign.Ok3 p)
    {s : State} (h : (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pre s) :
    vPre p 48 s ∧ Sign.StaticRoots 48 s ∧
      (s.gpr .x5 ≠ 0 → PublicCache p 48 s (verifyingMetadata s)) :=
  shared_verify_optimized_input hp h

theorem verify_metadata_setup (s : State) :
    WP isa (.block [.addImm .x .x21 .x4 0, .addImm .x .x22 .x5 0]) s fun t =>
      VG.Proof.MlKem.AArch64.Only [.x21, .x22] s t ∧
      t.gpr .x21 = s.gpr .x4 ∧ t.gpr .x22 = s.gpr .x5 := by
  open VG.Proof.MlKem.AArch64 in
  refine wp_addImm (by decide) fun u hu h21 => wp_addImm (by decide) fun t ht h22 => wp_nil ?_
  exact ⟨(hu.trans ht).mono (by simp), by rw [ht.get .x21, h21, BitVec.add_zero],
    by rw [h22, BitVec.add_zero, hu.get .x5]⟩

theorem setup_verify_inputs {p : Params} (hp : Sign.Ok3 p)
    {σ s : State} (hpre : (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pre σ)
    (hs : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signInner σ) s)
    (h21 : s.gpr .x21 = σ.gpr .x4) (h22 : s.gpr .x22 = σ.gpr .x5) (hy : s.syms = σ.syms) :
    (verifyCoreK p).pre s ∧ vPk p s = vPk p σ ∧
      vMu s = vMu σ ∧ vSig p s = vSig p σ := by
  obtain ⟨pre, roots, cached⟩ := shared_verify_input hp hpre
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
    rw [toNat_sub_ofNat' (by omega_using [hsp])]
    omega_using [hsp]
  · intro R hR
    rw [er]
    apply pre.2 R
    simpa only [vInputs, e0, e1, e2] using hR
  · have hr := roots
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
    have h2 := below_sub (sp := σ.sp) (a := 16 + offset) (b := 48) (by omega_using [ho]) (by decide)
    rw [hsp]
    exact fun a ha => h2 a (h1 a ha)
  refine ⟨?_, ?_⟩
  · rw [hsp, toNat_sub_ofNat' (by omega_using [ho, hstack])]
    omega_using [ho, hstack]
  · intro R hR
    rw [hw, hwr] at hR
    obtain rfl := List.mem_singleton.mp hR
    exact k4.sub_left hsub

theorem verify_withCache_correct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    (σ : State) (hpre : (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pre σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
      (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) σ tr t ∧ abiPreserved σ t ∧
      (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).post σ t := by
  have pre := (shared_verify_input hp hpre).1
  have hd := common_frame_bounds (verify_core_dle v p).le
  have g0 := verify_frame_guards (s := σ) pre (offset := 0) (by decide) rfl (by simp)
  have g1 := verify_frame_guards (s := pushState .x21 σ) pre (offset := 16) (by decide) rfl rfl
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
      (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) σ
      fun t => abiPreserved σ t ∧ (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).post σ t := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.withCache
    refine WP.frameReg g0.1 g0.2 ?_ (by
      simpa only [Code.aarch64Depth, Instr.frameUnits, Nat.zero_max] using hd.1)
    refine WP.frameReg g1.1 g1.2 ?_ (by
      simpa only [Code.aarch64Depth, Nat.zero_max] using hd.2)
    refine WP.seq (WP.mono_syms (verify_metadata_setup (signInner σ)) fun s ⟨hs, h21, h22⟩ hy => ?_)
    obtain ⟨hcore, hpk, hmu, hsig⟩ := setup_verify_inputs hp hpre hs h21 h22 hy
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
      have hab : Verify.OptimizedSelected.selectedAbi = abi.withConsts Sign.signRootConsts := rfl
      rw [hab]
      sig_post [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs,
        Abi.withConsts, Sign.signRootConsts_eq]
      simpa [vPk, vMu, vSig, State.write] using hpost
  obtain ⟨tr, t, he, habi, hpost⟩ := main
  exact ⟨tr, t, he, habi, hpost⟩

theorem shared_verify_pub {p : Params} {x y : State}
    (h : (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pub x y) :
    vPub p 48 x y ∧ (x.gpr .x4 = y.gpr .x4 ∧ x.gpr .x5 = y.gpr .x5) ∧ Sign.RootSymbolsEq x y := by
  have hab : Verify.OptimizedSelected.selectedAbi = abi.withConsts Sign.signRootConsts := rfl
  rw [hab] at h
  sig_pub_keep [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs,
    Abi.withConsts, Sign.signRootConsts_eq] at h
  obtain ⟨hsp, hd, hf, hi, hb, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ⟨h4, h5⟩, ⟨hf, hi⟩⟩
  sig_pub [vPub, verifyContract, verifySig, abi, VG.AArch64.argRegs]
  exact ⟨hsp, hd, hb, h0, h1, h2, h3⟩

def SharedVerifyRel (p : Params) (x y : State) : Prop :=
  (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pre x ∧
  (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pre y ∧
  (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pub x y

theorem setup_verify_pub {p : Params} (hp : Sign.Ok3 p)
    {σ τ x y : State} (h : SharedVerifyRel p σ τ)
    (hx : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signPushed σ) x)
    (hy : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signPushed τ) y)
    (x21 : x.gpr .x21 = σ.gpr .x4) (x22 : x.gpr .x22 = σ.gpr .x5)
    (y21 : y.gpr .x21 = τ.gpr .x4) (y22 : y.gpr .x22 = τ.gpr .x5)
    (xs : x.syms = σ.syms) (ys : y.syms = τ.syms) (dx : x.dit = σ.dit) (dy : y.dit = τ.dit) :
    (verifyCoreK p).pub (x.withRegions σ.rd σ.wr) (y.withRegions τ.rd τ.wr) := by
  have nx := setup_verify_inputs hp h.1 (sign_setup_narrow hx) x21 x22 xs
  have ny := setup_verify_inputs hp h.2.1 (sign_setup_narrow hy) y21 y22 ys
  obtain ⟨pub, ⟨h4, h5⟩, roots⟩ := shared_verify_pub h.2.2
  obtain ⟨hsp, hpk, hmu, hsig, h0, h1, h2, h3⟩ := vPub_eq pub
  have esp : x.sp = y.sp := by
    rw [hx.sp, hy.sp]
    change (σ.sp - 16) - 16 = (τ.sp - 16) - 16
    rw [hsp]
  refine ⟨?_, ?_, ?_⟩
  · sig_pub [vPub, verifyContract, verifySig, abi, VG.AArch64.argRegs]
    refine ⟨esp, dx.trans ((vPub_dit pub).trans dy.symm), ?_, ?_, ?_, ?_, ?_⟩
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
  · simpa only [Sign.RootSymbolsEq, State.withRegions, xs, ys] using roots
  · refine ⟨fun r hr => ?_, esp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact x21.trans (h4.trans y21.symm)
    · exact x22.trans (h5.trans y22.symm)

theorem verify_withCache_ct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p) :
    ConstantTime isa (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pre
      (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pub
      (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  have hs : ∀ x y, SharedVerifyRel p x y → x.sp = y.sp := by
    intro x y h
    exact (vPub_eq (shared_verify_pub h.2.2).1).1
  have trace : RelCT isa (SharedVerifyRel p)
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
        have pub := shared_verify_pub h.2.2
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
        have nx := setup_verify_inputs hp h.1 (sign_setup_narrow hx) x21 x22 xs
        have ny := setup_verify_inputs hp h.2.1 (sign_setup_narrow hy) y21 y22 ys
        have rx : Covers (σ.rd ++ σ.wr) (x.rd ++ x.wr) := by
          rw [hx.rd, hx.wr]
          exact Covers.append (Covers.refl _) (signPushed_wr_cover σ)
        have ry : Covers (τ.rd ++ τ.wr) (y.rd ++ y.wr) := by
          rw [hy.rd, hy.wr]
          exact Covers.append (Covers.refl _) (signPushed_wr_cover τ)
        have wx : Covers σ.wr x.wr := by rw [hx.wr]; exact signPushed_wr_cover σ
        have wy : Covers τ.wr y.wr := by rw [hy.wr]; exact signPushed_wr_cover τ
        have px : (verifyCoreK p).pre (x.withRegions σ.rd σ.wr) := nx.1
        have py : (verifyCoreK p).pre (y.withRegions τ.rd τ.wr) := ny.1
        obtain ⟨u, eu⟩ := trace_narrow (verify_core_correct v hp) px rx wx bx
        obtain ⟨w, ew⟩ := trace_narrow (verify_core_correct v hp) py ry wy by'
        have hp' := setup_verify_pub hp h hx hy x21 x22 y21 y22
          xs ys (by have := Exec.dit (c := .block [.addImm .x .x21 .x4 0, .addImm .x .x22 .x5 0]) (by decide) ax; exact this)
          (by have := Exec.dit (c := .block [.addImm .x .x21 .x4 0, .addImm .x .x22 .x5 0]) (by decide) ay; exact this)
        have hc := verify_core_ct v hp _ _ _ _ _ _ px py hp' eu ew
        exact ⟨by rw [hmeta, hc], trivial⟩
  intro x y tx ty x' y' hx hy hpub ex ey
  exact (trace _ _ _ _ _ _ ⟨hx, hy, hpub⟩ ex ey).1


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
      dsimp only [Sig.bufs, Sig.lists, Sig.alignedBufs, Elem.size]
      rfl
    · change (48 ≤ (524288#64).toNat ∧ _ ∧ _ ∧ _ ∧ _) ∧ _
      refine ⟨⟨by decide, ?_, held, ?_, ?_⟩, Or.inl rfl⟩
      all_goals
        simp only [sharedVerifySatWith, Verify.Optimized.verifySatWith, Verify.Optimized.baseSat,
          abi, regions, stackBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        sig_and_intros
        all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide +kernel

theorem shared_verify_sat {p : Params} (hp : Sign.Ok3 p) :
    ∃ s, (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48).pre s := by
  have hab : Verify.OptimizedSelected.selectedAbi = abi.withConsts Sign.signRootConsts := rfl
  rw [hab]
  have roots := (Sign.pairedRoots_entry (by decide) (Sign.pairedSign_sat hp)).2.1
  exact ⟨sharedVerifySatWith p (Sign.pairedSignSat p).mem,
    sharedVerifySatWith_pre p hp _ roots.forward.held roots.inverse.held⟩

theorem verify_withCache_verified (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) (hp : Sign.Ok3 p) :
    Verified AArch64.target (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
      (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p)
      (verifyWithCacheContract p (Verify.OptimizedSelected.selectedAbi) 48) :=
  ⟨verify_withCache_correct v hp, verify_withCache_ct v hp, shared_verify_sat hp⟩

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

theorem movV_noWriteDit (d : Reg) (v : Nat) : ∀ i ∈ movV d v, i.writesDit = false := by
  intro i hi
  unfold movV Impl.MlKem.AArch64.movImm at hi
  split at hi <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem lea_noWriteDit (d b : Reg) (off : Nat) : ∀ i ∈ lea d b off, i.writesDit = false := by
  intro i hi
  unfold lea at hi
  split at hi
  · simp only [List.mem_singleton] at hi; subst hi; rfl
  · rcases List.mem_append.mp hi with hi | hi
    · exact movV_noWriteDit d off i hi
    · simp only [List.mem_singleton] at hi; subst hi; rfl

/-- The setup never writes PSTATE.DIT (`Exec.dit`). -/
theorem operationSetup_noWriteDit (p : Params) (sign prepared : Bool) :
    (Code.block (operationSetup p sign prepared) : Prog isa).all (fun i => !i.writesDit) = true := by
  simp only [Code.all, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  intro i hi
  unfold operationSetup at hi
  split at hi <;> split at hi <;> rcases List.mem_append.mp hi with hi | hi
  all_goals first
    | exact lea_noWriteDit _ _ _ i hi
    | exact movV_noWriteDit _ _ i hi
    | (simp only [List.mem_singleton] at hi; subst hi; rfl)

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
    Code.aarch64Depth, Nat.zero_max, Instr.frameUnits] using Nat.add_le_add_right hd 2, by
    simp only [Impl.MlDsa.AArch64.PreparedKey.Sign.withCache, Code.all, (core_dle v hp).nd, Bool.and_true]
    rfl⟩

theorem verify_withCache_dle (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) : Message.DLe 3
      (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
        (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  have hd := (verify_core_dle v p).le
  exact ⟨by simpa only [Impl.MlDsa.AArch64.PreparedKey.Verify.withCache,
    Code.aarch64Depth, Nat.zero_max, Instr.frameUnits] using Nat.add_le_add_right hd 2, by
    simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.withCache, Code.all, (verify_core_dle v p).nd,
      Bool.and_true]
    rfl⟩

theorem prepared_public_cache_frame {p : Params} {m m' : Mem} {key : Addr} {W : List Region}
    (h : PreparedPublicKey p m key) (hf : Frame W m m')
    (hd : ∀ R ∈ W, (⟨key, preparedPublicKeyBytes p⟩ : Region).Disjoint R)
    (hb : preparedPublicKeyBytes p < 2 ^ 32) :
    CachedPublicPolys p m' (key + BitVec.ofNat 64 p.pkLen)
      (VG.Spec.Sha3.bytesAt m' key p.pkLen) := by
  have hs : Region.Sub (⟨key, p.pkLen⟩ : Region) ⟨key, preparedPublicKeyBytes p⟩ :=
    Region.sub_prefix (by simp only [preparedPublicKeyBytes]; omega_using [])
  have hk := VG.Proof.MlKem.bytesAt_frame hf (fun R hR => (hd R hR).sub_left hs)
    (by simp only [preparedPublicKeyBytes] at hb; omega_using [hb])
  intro i hi
  change PolyIs m' ((key + BitVec.ofNat 64 p.pkLen) + BitVec.ofNat 64 (4 * n * i)) _
  rw [VG.Offset.add_add, hk]
  exact VG.Proof.MlDsa.Verify.polyIs_frame hf (fun R hR => (hd R hR).sub_left
    (by
      change Region.Sub ⟨key + BitVec.ofNat 64 (p.pkLen + 4 * n * i), 1024⟩ _
      apply VG.Offset.sub_base key
      simp only [preparedPublicKeyBytes, n]
      omega_using [hi])) (VG.Proof.MlDsa.preparedPublicKey_iff.1 h i hi)

theorem prepared_secret_cache_frame {p : Params} {m m' : Mem} {key : Addr} {W : List Region}
    (h : PreparedSecretKey p m key) (hf : Frame W m m')
    (hd : ∀ R ∈ W, (⟨key, preparedSecretKeyBytes p⟩ : Region).Disjoint R)
    (hb : preparedSecretKeyBytes p < 2 ^ 32) :
    CachedSecretPolys p m' (key + BitVec.ofNat 64 p.skLen)
      (VG.Spec.Sha3.bytesAt m' key p.skLen) := by
  have hs : Region.Sub (⟨key, p.skLen⟩ : Region) ⟨key, preparedSecretKeyBytes p⟩ :=
    Region.sub_prefix (by simp only [preparedSecretKeyBytes]; omega_using [])
  have hk := VG.Proof.MlKem.bytesAt_frame hf (fun R hR => (hd R hR).sub_left hs)
    (by simp only [preparedSecretKeyBytes] at hb; omega_using [hb])
  intro i hi
  change PolyIs m' ((key + BitVec.ofNat 64 p.skLen) + BitVec.ofNat 64 (4 * n * i)) _
  rw [VG.Offset.add_add, hk]
  exact VG.Proof.MlDsa.Verify.polyIs_frame hf (fun R hR => (hd R hR).sub_left
    (by
      change Region.Sub ⟨key + BitVec.ofNat 64 (p.skLen + 4 * n * i), 1024⟩ _
      apply VG.Offset.sub_base key
      simp only [preparedSecretKeyBytes, n]
      omega_using [hi])) (VG.Proof.MlDsa.preparedSecretKey_iff.1 h i hi)

def verifyEntryRd (p : Params) (s : State) : List Region :=
  [⟨s.gpr .x0, p.pkLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, p.sigLen⟩,
    ⟨s.gpr .x4, (s.gpr .x5).toNat⟩]

theorem empty_disjoint (a : Addr) (r : Region) : (⟨a, 0⟩ : Region).Disjoint r := by
  intro x hx _
  simp only [Region.Contains] at hx
  omega_using [hx]

theorem verify_empty_pre {p : Params} {σ s : State}
    (pre : (verifyContract p abi 64).pre σ)
    (o : Only [.x4, .x5] (pushState .x30 σ) s)
    (h4 : s.gpr .x4 = σ.gpr .x0) (h5 : s.gpr .x5 = 0) :
    (verifyWithCacheContract p abi 48).pre
      (s.callEntry.withRegions (verifyEntryRd p s) σ.wr) := by
  sig_pre [verifyContract, verifySig, abi, VG.AArch64.argRegs] at pre
  sig_split pre
  rename_i sp rd wr d1 d2 d3 k1 k2 k3 k4 n1 n2 n3
  have n4 := pre
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
    rw [toNat_sub_ofNat' (by omega_using [sp])]
    omega_using [sp]
  sig_pre [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs]
  simp only [verifyEntryRd, h4, h5,
    e0, e1, e2, e3, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
  exact ⟨sn, True.intro, wr, d1, d2, d3, (empty_disjoint _ _).symm,
    k1.sub_left ks, k2.sub_left ks, k3.sub_left ks, k4.sub_left ks,
    (empty_disjoint _ _).symm, n1, n2, n3, n4,
    by have := (σ.gpr .x0).isLt; omega_using [], Or.inl True.intro⟩

theorem verify_prepared_pre {p : Params} (hp : Sign.Ok3 p) {σ s : State}
    (pre : (preparedVerifyContract p abi 64).pre σ)
    (o : Only [.x4, .x5] (pushState .x30 σ) s)
    (h4 : s.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 p.pkLen)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (1024 * p.k)) :
    (verifyWithCacheContract p abi 48).pre
      (s.callEntry.withRegions (verifyEntryRd p s) σ.wr) := by
  sig_pre [preparedVerifyContract, preparedVerifySig, abi, VG.AArch64.argRegs] at pre
  sig_split pre
  rename_i sp rd wr d1 d2 d3 k1 k2 k3 k4 n1 n2 n3 n4
  have cached := pre
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
    simp only [preparedPublicKeyBytes]; omega_using [])
  have suffix : Region.Sub (⟨σ.gpr .x0 + BitVec.ofNat 64 p.pkLen, 1024 * p.k⟩ : Region)
      ⟨σ.gpr .x0, preparedPublicKeyBytes p⟩ := Offset.sub_base _ (by
    simp only [preparedPublicKeyBytes, hn]; omega_using [])
  have sn : 48 ≤ s.sp.toNat := by
    rw [esp]
    change 48 ≤ (σ.sp - BitVec.ofNat 64 16).toNat
    rw [toNat_sub_ofNat' (by omega_using [sp])]
    omega_using [sp]
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
    omega_using [n1]
  have nsuffix : (σ.gpr .x0 + BitVec.ofNat 64 p.pkLen).toNat + 1024 * p.k ≤ 2 ^ 64 := by
    have bound : (σ.gpr .x0 + BitVec.ofNat 64 p.pkLen).toNat ≤
        (σ.gpr .x0).toNat + p.pkLen := by
      rw [Offset.toNat_add_ofNat]
      exact (Nat.mod_le _ _).trans (Nat.add_le_add_left (Nat.mod_le _ _) _)
    simp only [preparedPublicKeyBytes, hn] at n1
    omega_using [bound, n1]
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
  sig_split pre
  rename_i sp rd wr d1 d2 d3 d4 d5 d6 d7 k1 k2 k3 k4 k5 n1 n2 n3 n4
  have n5 := pre
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
    rw [toNat_sub_ofNat' (by omega_using [sp])]
    omega_using [sp]
  sig_pre [signWithCacheContract, signWithCacheSig, signSig, abi, VG.AArch64.argRegs]
  simp only [signEntryRd, h5, h6, e0, e1, e2, e3, e4,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
  exact ⟨sn, True.intro, wr, d1, d2, d3, d4, d5, d6, d7,
    (empty_disjoint _ _).symm, (empty_disjoint _ _).symm,
    k1.sub_left ks, k2.sub_left ks, k3.sub_left ks, k4.sub_left ks, k5.sub_left ks,
    (empty_disjoint _ _).symm, n1, n2, n3, n4, n5,
    by have := (σ.gpr .x0).isLt; omega_using [], Or.inl True.intro⟩

theorem sign_prepared_pre {p : Params} (hp : Sign.Ok3 p) {σ s : State}
    (pre : (preparedSignContract p abi 64).pre σ)
    (o : Only [.x5, .x6] (pushState .x30 σ) s)
    (h5 : s.gpr .x5 = σ.gpr .x0 + BitVec.ofNat 64 p.skLen)
    (h6 : s.gpr .x6 = BitVec.ofNat 64 (1024 * (p.ℓ + 2 * p.k))) :
    (signWithCacheContract p abi 48).pre
      (s.callEntry.withRegions (signEntryRd p s) σ.wr) := by
  sig_pre [preparedSignContract, preparedSignSig, abi, VG.AArch64.argRegs] at pre
  sig_split pre
  rename_i sp rd wr d1 d2 d3 d4 d5 d6 d7 k1 k2 k3 k4 k5 n1 n2 n3 n4 n5
  have cached := pre
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
    simp only [preparedSecretKeyBytes]; omega_using [])
  have suffix : Region.Sub (⟨σ.gpr .x0 + BitVec.ofNat 64 p.skLen, 1024 * (p.ℓ + 2 * p.k)⟩ : Region)
      ⟨σ.gpr .x0, preparedSecretKeyBytes p⟩ := Offset.sub_base _ (by
    simp only [preparedSecretKeyBytes, hn]; omega_using [])
  have sn : 48 ≤ s.sp.toNat := by
    rw [esp]
    change 48 ≤ (σ.sp - BitVec.ofNat 64 16).toNat
    rw [toNat_sub_ofNat' (by omega_using [sp])]
    omega_using [sp]
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
    omega_using [n1]
  have nsuffix : (σ.gpr .x0 + BitVec.ofNat 64 p.skLen).toNat + 1024 * (p.ℓ + 2 * p.k) ≤ 2 ^ 64 := by
    have bound : (σ.gpr .x0 + BitVec.ofNat 64 p.skLen).toNat ≤
        (σ.gpr .x0).toNat + p.skLen := by
      rw [Offset.toNat_add_ofNat]
      exact (Nat.mod_le _ _).trans (Nat.add_le_add_left (Nat.mod_le _ _) _)
    simp only [preparedSecretKeyBytes, hn] at n1
    omega_using [bound, n1]
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
    · exact ⟨⟨σ.gpr .x2, p.sigLen⟩, by simp, 0, by simpa using e2, by change 0 + p.sigLen ≤ p.sigLen; omega_using []⟩
    · refine ⟨⟨σ.gpr .x0, rawVerifyBytes p prepared⟩, by simp,
        (if prepared then p.pkLen else 0), h4, ?_⟩
      rw [h5]
      cases prepared
      · change 0 + (0 : BitVec 64).toNat ≤ p.pkLen
        exact Nat.zero_le _
      · have hm : (BitVec.ofNat 64 (1024 * p.k)).toNat ≤ 1024 * p.k := Nat.mod_le _ _
        simp only [rawVerifyBytes, ↓reduceIte, preparedPublicKeyBytes, n]
        omega_using [hm]
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
  omega_using [bound]

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
    (y5 : y.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0))
    (dx : x.dit = σ.dit) (dy : y.dit = τ.dit) :
    (verifyWithCacheContract p abi 48).pub
      (x.callEntry.withRegions (verifyEntryRd p x) σ.wr)
      (y.callEntry.withRegions (verifyEntryRd p y) τ.wr) := by
  have hd : σ.dit = τ.dit := by
    cases prepared
    all_goals
      simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte] at pub
      sig_pub_keep [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
        abi, VG.AArch64.argRegs] at pub
      exact pub.2.1
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
  refine ⟨?_, dx.trans (hd.trans dy.symm), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

theorem verify_entry_bases {p : Params} {prepared : Bool} {x y : State}
    (h : (rawVerifyK p prepared abi).pub x y) : SameIn [.x0] x y := by
  cases prepared
  all_goals
    simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pub [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
      abi, VG.AArch64.argRegs] at h
    exact ⟨fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.2.2.1, h.1⟩

theorem operation_narrow {R : List Reg} {σ s : State} (o : Only R (pushed .x30 σ) s) :
    Only R (pushState .x30 σ) (s.withRegions σ.rd σ.wr) :=
  ⟨o.gpr, o.mem, rfl, rfl, o.sp, o.vcs⟩

theorem operation_cover {R : List Reg} {σ s : State} (o : Only R (pushed .x30 σ) s) :
    Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr) := by
  rw [o.rd, o.wr]
  exact Covers.append (Covers.refl _) (push_wr_cover .x30 σ)

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

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## Restoring constant-table preconditions at shared calls -/

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Sign

theorem sign_cache_pre_extend {p : Params} {s : State}
    (h : (signWithCacheContract p abi 48).pre (s.withRegions (signEntryRd p s) s.wr))
    (hr : StaticRoots 48 s) (rp : PairedRoots 48 s)
    (hd : s.rd = signEntryRd p s ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,
        ⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]) :
    (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre s := by
  sig_pre [signWithCacheContract, signWithCacheSig, signSig, abi, VG.AArch64.argRegs] at h
  sig_pre [signWithCacheContract, signWithCacheSig, signSig, abi, VG.AArch64.argRegs,
    Abi.withConsts, pairedSignRootConsts_eq, Abi.constRegions, Abi.constsHeld,
    TableConstants.staticNttWords_length, InverseTable.expandedWords_length,
    PairedTable.expandedWords_length, stackBelow]
  obtain ⟨sp, _rd, wr, d1, d2, d3, d4, d5, d6, d7, dc1, dc2,
    k1, k2, k3, k4, k5, kc, n1, n2, n3, n4, n5, nc, cache⟩ := h
  exact ⟨sp,by rw [hd]; rfl,hr.forward.held,hr.inverse.held,rp.held,
    hr.forward.fit,hr.forward.writable,hr.forward.stack,hr.inverse.fit,hr.inverse.writable,
    hr.inverse.stack,rp.fit,rp.writable,rp.stack,hr.forward.aligned,hr.inverse.aligned,
    rp.aligned,by rw [hd]; rfl,wr,d1,d2,d3,d4,d5,d6,d7,dc1,dc2,
    k1,k2,k3,k4,k5,kc,n1,n2,n3,n4,n5,nc,cache⟩

theorem verify_cache_pre_extend {p : Params} {s : State}
    (h : (verifyWithCacheContract p abi 48).pre (s.withRegions (verifyEntryRd p s) s.wr))
    (hr : StaticRoots 48 s)
    (hd : s.rd = verifyEntryRd p s ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩]) :
    (verifyWithCacheContract p (abi.withConsts signRootConsts) 48).pre s := by
  sig_pre [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs] at h
  sig_pre [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs,
    Abi.withConsts, signRootConsts_eq, Abi.constRegions, Abi.constsHeld,
    TableConstants.staticNttWords_length, InverseTable.expandedWords_length, stackBelow]
  obtain ⟨sp, _rd, wr, d1, d2, d3, dc, k1, k2, k3, k4, kc, n1, n2, n3, n4, nc, cache⟩ := h
  exact ⟨sp,by rw [hd]; rfl,hr.forward.held,hr.inverse.held,hr.forward.fit,
    hr.forward.writable,hr.forward.stack,hr.inverse.fit,hr.inverse.writable,
    hr.inverse.stack,hr.forward.aligned,hr.inverse.aligned,by rw [hd]; rfl,
    wr,d1,d2,d3,dc,k1,k2,k3,k4,kc,n1,n2,n3,n4,nc,cache⟩
end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only)

theorem operation_saved_frame {R : List Reg} {σ s : State}
    (o : Only R (pushState .x30 σ) s) : Frame [below σ.sp 16] σ.mem s.mem := by
  rw [o.mem]
  exact Frame.write (r := below σ.sp 16) (Frame.refl _ _) (by simp) _
    (by simp [Region.Contains])

theorem operation_static_roots {R : List Reg} {σ s : State}
    (h : StaticRoots 64 σ) (o : Only R (pushState .x30 σ) s) (hy : s.syms = σ.syms) :
    StaticRoots 48 s := by
  have stackSub : Region.Sub (below s.sp 48) (below σ.sp 64) := by
    rw [o.sp]
    exact below_below σ.sp 16 48
  have pass {nm : String} {ws : List (BitVec 64)} (ht : StaticTable 64 nm ws σ) :
      StaticTable 48 nm ws s := by
    apply staticTable_reframe ht (operation_saved_frame o) ?_ o.rd o.wr hy stackSub
    intro T hT
    obtain rfl := List.mem_singleton.mp hT
    exact ht.stack.sub_right (below_sub (by decide) (by decide))
  exact ⟨pass h.forward, pass h.inverse⟩

theorem operation_paired_roots {R : List Reg} {σ s : State}
    (h : PairedRoots 64 σ) (o : Only R (pushState .x30 σ) s) (hy : s.syms = σ.syms) :
    PairedRoots 48 s := by
  have stackSub : Region.Sub (below s.sp 48) (below σ.sp 64) := by
    rw [o.sp]
    exact below_below σ.sp 16 48
  apply pairedRoots_reframe h (operation_saved_frame o) ?_ o.rd o.wr hy stackSub
  intro T hT
  obtain rfl := List.mem_singleton.mp hT
  exact h.stack.sub_right (below_sub (by decide) (by decide))

theorem operation_table_reborrow {S : Nat} {nm : String} {ws : List (BitVec 64)}
    {s : State} {rd wr : List Region} (h : StaticTable S nm ws s)
    (hm : (⟨s.syms nm, 3904⟩ : Region) ∈ rd) (hw : Covers wr s.wr) :
    StaticTable S nm ws (s.callEntry.withRegions rd wr) := by
  refine ⟨h.held, h.fit, ?_, ?_, h.stack, h.aligned⟩
  · exact Covers.one ⟨⟨s.syms nm, 3904⟩, List.mem_append_left _ hm, Region.contains_self _ _⟩
  · intro T hT
    exact h.apart_write (hw T.base T.len ⟨T, hT, Region.contains_self _ _⟩)

theorem operation_pair_reborrow {S : Nat} {s : State} {rd wr : List Region}
    (h : PairedRoots S s) (hm : (⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩ : Region) ∈ rd)
    (hw : Covers wr s.wr) : PairedRoots S (s.callEntry.withRegions rd wr) := by
  refine ⟨h.held, h.fit, ?_, ?_, h.stack, h.aligned⟩
  · exact Covers.one ⟨⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩,
      List.mem_append_left _ hm, Region.contains_self _ _⟩
  · intro T hT
    exact h.apart_write (hw T.base T.len ⟨T, hT, Region.contains_self _ _⟩)

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

def rawVerifyRd (p : Params) (prepared : Bool) (s : State) : List Region :=
  [⟨s.gpr .x0, rawVerifyBytes p prepared⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, p.sigLen⟩]

def verifyRootRd (s : State) : List Region :=
  [⟨s.syms "VG_MLDSA_NTT_EXPANDED", 3904⟩, ⟨s.syms "VG_MLDSA_INV_FOLDED", 3904⟩]

theorem raw_verify_constants {p : Params} {prepared : Bool} {σ : State}
    (pre : (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre σ) :
    (rawVerifyK p prepared abi).pre (σ.withRegions (rawVerifyRd p prepared σ) σ.wr) ∧
    StaticRoots 64 σ ∧ σ.rd = rawVerifyRd p prepared σ ++ verifyRootRd σ := by
  cases prepared
  all_goals
    simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte] at pre ⊢
    sig_pre [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
      abi, VG.AArch64.argRegs, Abi.withConsts, signRootConsts_eq, Abi.constRegions,
      Abi.constsHeld, TableConstants.staticNttWords_length,
      InverseTable.expandedWords_length, stackBelow] at pre
    obtain ⟨sp, hd, hf, hi, hff, hfw, hfs, hif, hiw, his, hfa, hia, ht, hw,
      d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, tail⟩ := pre
    have rd := (List.take_append_drop (σ.rd.length - 2) σ.rd).symm
    rw [ht, hd] at rd
    refine ⟨?_, ⟨⟨hf, hff, ?_, hfw, hfs, hfa⟩, ⟨hi, hif, ?_, hiw, his, hia⟩⟩, rd⟩
    · sig_pre [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
        abi, VG.AArch64.argRegs]
      exact ⟨sp, rfl, hw, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, tail⟩
    · apply Covers.one
      exact ⟨⟨σ.syms "VG_MLDSA_NTT_EXPANDED", 3904⟩,
        List.mem_append_left _ (by rw [rd]; simp), Region.contains_self _ _⟩
    · apply Covers.one
      exact ⟨⟨σ.syms "VG_MLDSA_INV_FOLDED", 3904⟩,
        List.mem_append_left _ (by rw [rd]; simp), Region.contains_self _ _⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only)

theorem operation_reset_rd {R : List Reg} {σ s : State}
    (o : Only R (pushState .x30 σ) s) (rd : List Region) :
    Only R (pushState .x30 (σ.withRegions rd σ.wr)) (s.withRegions rd σ.wr) :=
  ⟨o.gpr, o.mem, rfl, rfl, o.sp, o.vcs⟩

theorem verify_entry_constants_pre {p : Params} (hp : Ok3 p) {prepared : Bool} {σ s : State}
    (pre : (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre σ)
    (o : Only [.x4, .x5] (pushState .x30 σ) s) (hy : s.syms = σ.syms)
    (h4 : s.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0))
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0)) :
    (verifyWithCacheContract p (abi.withConsts signRootConsts) 48).pre
      (s.callEntry.withRegions (verifyEntryRd p s ++ verifyRootRd s) σ.wr) := by
  have resources := raw_verify_constants pre
  have ob := operation_reset_rd o (rawVerifyRd p prepared σ)
  have base := verify_entry_pre hp resources.1 ob h4 h5
  have roots := operation_static_roots resources.2.1 o hy
  have hw : Covers σ.wr s.wr := by rw [o.wr]; exact Covers.refl _
  have ntt : (⟨s.syms "VG_MLDSA_NTT_EXPANDED", 3904⟩ : Region) ∈
      verifyEntryRd p s ++ verifyRootRd s := by simp [verifyRootRd]
  have inv : (⟨s.syms "VG_MLDSA_INV_FOLDED", 3904⟩ : Region) ∈
      verifyEntryRd p s ++ verifyRootRd s := by simp [verifyRootRd]
  have borrowed : StaticRoots 48
      (s.callEntry.withRegions (verifyEntryRd p s ++ verifyRootRd s) σ.wr) :=
    ⟨operation_table_reborrow roots.forward ntt hw,
      operation_table_reborrow roots.inverse inv hw⟩
  apply verify_cache_pre_extend ?_ borrowed rfl
  simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
    verifyEntryRd, State.withRegions_gpr, State.withRegions_wr,
    State.callEntry_gpr _ (r := .x0) (by decide),
    State.callEntry_gpr _ (r := .x1) (by decide),
    State.callEntry_gpr _ (r := .x2) (by decide),
    State.callEntry_gpr _ (r := .x4) (by decide),
    State.callEntry_gpr _ (r := .x5) (by decide)] using base

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only)

theorem verify_entry_constants_covers {p : Params} {prepared : Bool} {σ s : State}
    (pre : (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre σ)
    (o : Only [.x4, .x5] (pushState .x30 σ) s) (hy : s.syms = σ.syms)
    (h4 : s.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0))
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0)) :
    Covers ((verifyEntryRd p s ++ verifyRootRd s) ++ σ.wr) (s.rd ++ s.wr) := by
  have resources := raw_verify_constants pre
  have ob := operation_reset_rd o (rawVerifyRd p prepared σ)
  have base := verify_entry_covers resources.1 ob h4 h5
  have lift : Covers (rawVerifyRd p prepared σ ++ σ.wr) (s.rd ++ s.wr) := by
    rw [o.rd, o.wr]
    change Covers (rawVerifyRd p prepared σ ++ σ.wr) (σ.rd ++ σ.wr)
    apply Covers.append
    · apply Covers.of_mem
      intro T hT
      rw [resources.2.2]
      exact List.mem_append_left _ hT
    · exact Covers.refl _
  have baseRead : Covers (verifyEntryRd p s) (s.rd ++ s.wr) := by
    intro a n ⟨T, hT, hC⟩
    apply lift a n
    exact base a n ⟨T, List.mem_append_left _ hT, hC⟩
  have rootRead : Covers (verifyRootRd s) (s.rd ++ s.wr) := by
    apply Covers.left
    apply Covers.of_mem
    intro T hT
    rw [o.rd, show (pushState .x30 σ).rd = σ.rd from rfl, resources.2.2]
    apply List.mem_append_right
    simpa only [verifyRootRd, hy] using hT
  exact Covers.append_left (Covers.append_left baseRead rootRead)
    (Covers.right (by rw [o.wr]; exact Covers.refl _))

theorem verify_entry_constants_correct {p : Params} (hp : Sign.Ok3 p) {name : String}
    {code : Prog isa} (hv : ∀ σ, (verifyWithCacheContract p (abi.withConsts signRootConsts) 48).pre σ →
      ∃ tr t, Exec isa code σ tr t ∧ abiPreserved σ t ∧
        (verifyWithCacheContract p (abi.withConsts signRootConsts) 48).post σ t)
    (hd : Message.DLe 3 code) (prepared : Bool) (σ : State)
    (pre : (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared) σ tr t ∧
      abiPreserved σ t ∧ (rawVerifyK p prepared (abi.withConsts signRootConsts)).post σ t := by
  have layout := verify_entry_layout (raw_verify_constants pre).1
  have depth := (operation_call_bounds hd).1
  have guard : ∀ R ∈ σ.wr, (below σ.sp 16).Disjoint R := by
    intro R hR
    have hw : σ.wr = [⟨σ.gpr .x3, scratchWords p * 8⟩] := layout.2.2.1
    rw [hw] at hR
    obtain rfl := List.mem_singleton.mp hR
    exact layout.2.2.2.2.2.2.sub_left (below_sub (by decide) (by decide))
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared) σ
      fun t => abiPreserved σ t ∧ (rawVerifyK p prepared (abi.withConsts signRootConsts)).post σ t := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.entry
    refine WP.frameReg (Nat.le_trans (by decide) layout.1) guard ?_ (by
      simpa only [Code.aarch64Depth, Nat.zero_max] using depth)
    change WP isa (.seq (.block (operationSetup p false prepared)) (.call name code)) (pushState .x30 σ) _
    refine WP.seq (WP.mono_syms (operationSetup_ok p false prepared (pushState .x30 σ)) fun s hs sy => ?_)
    have hc := verify_entry_constants_covers pre hs.1 sy hs.2.1 hs.2.2
    have hcpre := verify_entry_constants_pre hp pre hs.1 sy hs.2.1 hs.2.2
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
      have key := save_input_bytes (σ := σ) (r := .x30) (layout.2.2.2.1.sub_right keySub) keyB
      have mu := save_input_bytes (σ := σ) (key := σ.gpr .x1) (r := .x30) layout.2.2.2.2.1 (by decide)
      have sig := save_input_bytes (σ := σ) (key := σ.gpr .x2) (r := .x30) layout.2.2.2.2.2.1 sigB
      sig_post [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs, Abi.withConsts] at post
      simp only [e0, e1, e2, hs.1.mem, key, mu, sig] at post
      cases prepared
      all_goals
        simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte]
        sig_post [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
          abi, VG.AArch64.argRegs, Abi.withConsts]
        simpa only [State.write, reduceCtorEq, ite_false] using post
  obtain ⟨tr, t, he, habi, hpost⟩ := main
  exact ⟨tr, t, he, habi, hpost⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only)

theorem raw_verify_constants_pub {p : Params} {prepared : Bool} {x y : State}
    (h : (rawVerifyK p prepared (abi.withConsts signRootConsts)).pub x y) :
    (rawVerifyK p prepared abi).pub
      (x.withRegions (rawVerifyRd p prepared x) x.wr)
      (y.withRegions (rawVerifyRd p prepared y) y.wr) ∧
    x.syms "VG_MLDSA_NTT_EXPANDED" = y.syms "VG_MLDSA_NTT_EXPANDED" ∧
    x.syms "VG_MLDSA_INV_FOLDED" = y.syms "VG_MLDSA_INV_FOLDED" := by
  cases prepared
  all_goals
    simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte] at h ⊢
    sig_pub_keep [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
      abi, VG.AArch64.argRegs, Abi.withConsts, signRootConsts_eq] at h
    obtain ⟨sp, hd, hf, hi, leak, h0, h1, h2, h3⟩ := h
    refine ⟨?_, hf, hi⟩
    sig_pub [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
      abi, VG.AArch64.argRegs]
    exact ⟨sp, hd, leak, h0, h1, h2, h3⟩

theorem verify_entry_constants_pub {p : Params} (hp : Ok3 p) {prepared : Bool} {σ τ x y : State}
    (px : (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre σ)
    (py : (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre τ)
    (pub : (rawVerifyK p prepared (abi.withConsts signRootConsts)).pub σ τ)
    (ox : Only [.x4, .x5] (pushState .x30 σ) x)
    (oy : Only [.x4, .x5] (pushState .x30 τ) y)
    (sx : x.syms = σ.syms) (sy : y.syms = τ.syms)
    (x4 : x.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0))
    (x5 : x.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0))
    (y4 : y.gpr .x4 = τ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0))
    (y5 : y.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0))
    (dx : x.dit = σ.dit) (dy : y.dit = τ.dit) :
    (verifyWithCacheContract p (abi.withConsts signRootConsts) 48).pub
      (x.callEntry.withRegions (verifyEntryRd p x ++ verifyRootRd x) σ.wr)
      (y.callEntry.withRegions (verifyEntryRd p y ++ verifyRootRd y) τ.wr) := by
  have pub0 := raw_verify_constants_pub pub
  have base := verify_entry_pub hp (raw_verify_constants px).1 (raw_verify_constants py).1
    pub0.1 (operation_reset_rd ox _) (operation_reset_rd oy _) x4 x5 y4 y5 dx dy
  sig_pub_keep [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs] at base
  sig_pub [verifyWithCacheContract, verifyWithCacheSig, verifySig, abi, VG.AArch64.argRegs,
    Abi.withConsts, signRootConsts_eq]
  obtain ⟨sp, hd, leak, h0, h1, h2, h3, h4, h5⟩ := base
  exact ⟨sp, hd, by simpa only [sx, sy] using pub0.2.1,
    by simpa only [sx, sy] using pub0.2.2, leak, h0, h1, h2, h3, h4, h5⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only)

def RawVerifyConstRel (p : Params) (prepared : Bool) (x y : State) : Prop :=
  (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre x ∧
  (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre y ∧
  (rawVerifyK p prepared (abi.withConsts signRootConsts)).pub x y

def VerifyConstCallRel (p : Params) (prepared : Bool) (x y : State) : Prop :=
  ∃ σ τ, RawVerifyConstRel p prepared σ τ ∧
    Only [.x4, .x5] (pushed .x30 σ) x ∧ Only [.x4, .x5] (pushed .x30 τ) y ∧
    x.gpr .x4 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0) ∧
    x.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0) ∧
    y.gpr .x4 = τ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0) ∧
    y.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0) ∧
    x.syms = σ.syms ∧ y.syms = τ.syms ∧ x.dit = σ.dit ∧ y.dit = τ.dit

def VerifySetupOut (p : Params) (prepared : Bool) (s t : State) : Prop :=
  (Only [.x4, .x5] s t ∧
    t.gpr .x4 = s.gpr .x0 + BitVec.ofNat 64 (if prepared then p.pkLen else 0) ∧
    t.gpr .x5 = BitVec.ofNat 64 (if prepared then 1024 * p.k else 0)) ∧ t.syms = s.syms

theorem verify_setup_syms_ok (p : Params) (prepared : Bool) (s : State) :
    WP isa (.block (operationSetup p false prepared)) s (VerifySetupOut p prepared s) := by
  exact WP.mono_syms (operationSetup_ok p false prepared s) (fun _ h hy => ⟨h, hy⟩)

theorem operation_region_syms (s : State) (rd wr : List Region) :
    (s.withRegions rd wr).syms = s.syms := rfl

theorem verify_entry_constants_ct {p : Params} (hp : Ok3 p) {name : String} {code : Prog isa}
    (hv : ∀ σ, (verifyWithCacheContract p (abi.withConsts signRootConsts) 48).pre σ →
      ∃ tr t, Exec isa code σ tr t ∧ abiPreserved σ t ∧
        (verifyWithCacheContract p (abi.withConsts signRootConsts) 48).post σ t)
    (hct : ConstantTime isa (verifyWithCacheContract p (abi.withConsts signRootConsts) 48).pre
      (verifyWithCacheContract p (abi.withConsts signRootConsts) 48).pub code) (prepared : Bool) :
    ConstantTime isa (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre
      (rawVerifyK p prepared (abi.withConsts signRootConsts)).pub
      (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared) := by
  have hs : ∀ x y, RawVerifyConstRel p prepared x y → x.sp = y.sp :=
    fun _ _ h => (verify_entry_bases (raw_verify_constants_pub h.2.2).1).2
  have trace : RelCT isa (RawVerifyConstRel p prepared)
      (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared) (fun _ _ => True) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.entry
    refine frame_tr (R := fun _ _ => True) hs ?_
    change RelCT isa (PushRel .x30 (RawVerifyConstRel p prepared))
      (.seq (.block (operationSetup p false prepared)) (.call name code)) (fun _ _ => True)
    refine RelCT.seq (R := VerifyConstCallRel p prepared) (RelCT.postDep
      (RelCT.mono (operationSetup_tr hp false prepared) (fun x y h => ?_) (fun _ _ _ => trivial))
      (fun x y _ => ⟨WP.dit (operationSetup_noWriteDit _ _ _) (verify_setup_syms_ok p prepared x),
        WP.dit (operationSetup_noWriteDit _ _ _) (verify_setup_syms_ok p prepared y)⟩)
      (fun x y x' y' h hx hy => ?_)) ?_
    · rcases h with ⟨σ, τ, h, rfl, rfl⟩
      exact ⟨(verify_entry_bases (raw_verify_constants_pub h.2.2).1).1,
        congrArg (· - 16) (hs σ τ h)⟩
    · rcases h with ⟨σ, τ, h, rfl, rfl⟩
      exact ⟨σ, τ, h, hx.1.1.1, hy.1.1.1, hx.1.1.2.1, hx.1.1.2.2,
        hy.1.1.2.1, hy.1.1.2.2, hx.1.2, hy.1.2, hx.2, hy.2⟩
    · apply RelCT.callEx hv hct
      rintro x y ⟨σ, τ, h, ox, oy, x4, x5, y4, y5, sx, sy, dx, dy⟩
      have nx := operation_narrow ox
      have ny := operation_narrow oy
      refine ⟨verifyEntryRd p x ++ verifyRootRd x, σ.wr,
        verifyEntryRd p y ++ verifyRootRd y, τ.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have px := verify_entry_constants_pre hp h.1 nx sx x4 x5
        simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
          verifyEntryRd, verifyRootRd, State.withRegions_gpr, operation_region_syms] using px
      · have py := verify_entry_constants_pre hp h.2.1 ny sy y4 y5
        simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
          verifyEntryRd, verifyRootRd, State.withRegions_gpr, operation_region_syms] using py
      · have pub := verify_entry_constants_pub hp h.1 h.2.1 h.2.2 nx ny sx sy x4 x5 y4 y5 dx dy
        simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
          verifyEntryRd, verifyRootRd, State.withRegions_gpr, operation_region_syms] using pub
      · have cover := verify_entry_constants_covers h.1 nx sx x4 x5
        change Covers ((verifyEntryRd p x ++ verifyRootRd x) ++ σ.wr) (σ.rd ++ σ.wr) at cover
        exact cover.trans (operation_cover ox)
      · rw [ox.wr]; exact push_wr_cover .x30 σ
      · have cover := verify_entry_constants_covers h.2.1 ny sy y4 y5
        change Covers ((verifyEntryRd p y ++ verifyRootRd y) ++ τ.wr) (τ.rd ++ τ.wr) at cover
        exact cover.trans (operation_cover oy)
      · rw [oy.wr]; exact push_wr_cover .x30 τ
  intro x y tx ty x' y' hx hy hpub ex ey
  exact (trace x y tx ty x' y' ⟨hx, hy, hpub⟩ ex ey).1

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## Prepared verification entries have satisfiable layouts -/

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

def prepWithTables (p : Params) (m : Mem) : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x10000 | .x2 => 0x200000 | _ => 0
  sp := 0x1000000
  mem := m
  rd := [⟨0x1000, p.pkLen⟩]
  wr := [⟨0x10000, preparedPublicKeyBytes p⟩, ⟨0x200000, 1024⟩]

theorem prepWithTables_pre {p : Params} (hp : Ok3 p) (m : Mem) :
    (preparePublicKeyContract p abi 80).pre (prepWithTables p m) := by
  rcases hp with rfl | rfl | rfl
  all_goals
    sig_pre [preparePublicKeyContract, preparePublicKeySig, abi, VG.AArch64.argRegs]
    sig_and_intros
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide +kernel

theorem prepare_public_depth {p : Params} (hp : Ok3 p) :
    (Impl.MlDsa.AArch64.PreparedKey.preparePublic p).aarch64Depth ≤ 5 := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem public_preparation_preserves_roots {p : Params} (hp : Ok3 p) {m : Mem} {t : State}
    {tr : List Leak}
    (he : Exec isa (Impl.MlDsa.AArch64.PreparedKey.preparePublic p) (prepWithTables p m) tr t)
    {base : Addr} (hb : base = 1048576 ∨ base = 1052480) :
    ∀ i < 488, t.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
      m.readW (base + BitVec.ofNat 64 (8 * i)) 64 := by
  have depth := prepare_public_depth hp
  have bound : 16 * (Impl.MlDsa.AArch64.PreparedKey.preparePublic p).aarch64Depth < 2 ^ 64 := by omega_using [depth]
  have frame := Exec.frameSp he bound
  intro i hi
  apply frame.readW (r := ⟨base, 3904⟩)
    (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) ?_ (by decide)
  intro R hR
  simp only [prepWithTables, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · rcases hp with rfl | rfl | rfl <;> rcases hb with rfl | rfl
    all_goals exact Region.disjoint_of_sep (by decide)
  · rcases hb with rfl | rfl
    all_goals exact Region.disjoint_of_sep (by decide)
  · have hs : Region.Sub (below (0x1000000 : Addr)
        (16 * (Impl.MlDsa.AArch64.PreparedKey.preparePublic p).aarch64Depth))
        (below (0x1000000 : Addr) 80) := below_sub (by omega_using [depth]) (by decide)
    apply Region.Disjoint.sub_right _ hs
    rcases hb with rfl | rfl
    all_goals exact Region.disjoint_of_sep (by decide)
theorem raw_verify_pre_extend {p : Params} {prepared : Bool} {s : State}
    (h : (rawVerifyK p prepared abi).pre (s.withRegions (rawVerifyRd p prepared s) s.wr))
    (hr : StaticRoots 64 s) (hd : s.rd = rawVerifyRd p prepared s ++ verifyRootRd s) :
    (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre s := by
  cases prepared
  all_goals
    simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte] at h ⊢
    sig_pre [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
      abi, VG.AArch64.argRegs] at h
    sig_pre [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
      abi, VG.AArch64.argRegs, Abi.withConsts, signRootConsts_eq,
      Abi.constRegions, Abi.constsHeld, TableConstants.staticNttWords_length,
      InverseTable.expandedWords_length, stackBelow]
    obtain ⟨sp, _rd, wr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, tail⟩ := h
    exact ⟨sp,by rw [hd]; rfl,hr.forward.held,hr.inverse.held,hr.forward.fit,
      hr.forward.writable,hr.forward.stack,hr.inverse.fit,hr.inverse.writable,
      hr.inverse.stack,hr.forward.aligned,hr.inverse.aligned,by rw [hd]; rfl,
      wr,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,tail⟩

def rawVerifyConstSat (p : Params) (prepared : Bool) (m : Mem) : State :=
  { rawVerifySat p prepared m with
    syms := fun name => if name = "VG_MLDSA_NTT_EXPANDED" then 1048576 else 1052480
    rd := (rawVerifySat p prepared m).rd ++ [⟨1048576,3904⟩,⟨1052480,3904⟩] }

theorem rawVerifyConstSat_roots (p : Params) (hp : Ok3 p) (prepared : Bool) (m : Mem)
    (hf : ∀ i < 488, m.readW (1048576 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0)
    (hi : ∀ i < 488, m.readW (1052480 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0) :
    StaticRoots 64 (rawVerifyConstSat p prepared m) := by
  refine ⟨⟨hf, by dsimp [rawVerifyConstSat]; decide, ?_, ?_,
      by apply Region.disjoint_of_sep; dsimp [rawVerifyConstSat, rawVerifySat]; decide,
      by rw [show (rawVerifyConstSat p prepared m).syms "VG_MLDSA_NTT_EXPANDED" = 1048576 from rfl]; decide⟩,
    ⟨hi, by dsimp [rawVerifyConstSat]; decide, ?_, ?_,
      by apply Region.disjoint_of_sep; dsimp [rawVerifyConstSat, rawVerifySat]; decide,
      by rw [show (rawVerifyConstSat p prepared m).syms "VG_MLDSA_INV_FOLDED" = 1052480 from rfl]; decide⟩⟩
  · apply Covers.one
    exact ⟨⟨1048576,3904⟩, by simp [rawVerifyConstSat], Region.contains_self _ _⟩
  · rcases hp with rfl | rfl | rfl
    all_goals
      simp only [rawVerifyConstSat, rawVerifySat, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq]
      exact Region.disjoint_of_sep (by decide)
  · apply Covers.one
    exact ⟨⟨1052480,3904⟩, by simp [rawVerifyConstSat], Region.contains_self _ _⟩
  · rcases hp with rfl | rfl | rfl
    all_goals
      simp only [rawVerifyConstSat, rawVerifySat, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq]
      exact Region.disjoint_of_sep (by decide)

theorem rawVerifyConstSat_pre {p : Params} (hp : Ok3 p) (prepared : Bool) (m : Mem)
    (hf : ∀ i < 488, m.readW (1048576 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0)
    (hi : ∀ i < 488, m.readW (1052480 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (cache : prepared = true → PreparedPublicKey p m 0x10000) :
    (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre
      (rawVerifyConstSat p prepared m) := by
  apply raw_verify_pre_extend ?_ (rawVerifyConstSat_roots p hp prepared m hf hi) rfl
  have base := raw_verify_sat_pre hp prepared cache
  cases prepared
  all_goals
    simp only [rawVerifyK, Bool.false_eq_true, ↓reduceIte] at base ⊢
    sig_pre [verifyContract, verifySig, preparedVerifyContract, preparedVerifySig,
      abi, VG.AArch64.argRegs] at base ⊢
    exact base

theorem raw_verify_constants_sat {p : Params} (hp : Ok3 p) (prepared : Bool) :
    ∃ s, (rawVerifyK p prepared (abi.withConsts signRootConsts)).pre s := by
  have roots := (pairedRoots_entry (by decide) (pairedSign_sat hp)).2.1
  let m := (pairedSignSat p).mem
  have hf : ∀ i < 488, m.readW (1048576 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0 := roots.forward.held
  have hi : ∀ i < 488, m.readW (1052480 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0 := roots.inverse.held
  cases prepared
  · exact ⟨rawVerifyConstSat p false m,
      rawVerifyConstSat_pre hp false m hf hi (by intro h; cases h)⟩
  · obtain ⟨_, t, he, _, post⟩ := public_correct hp (prepWithTables p m) (prepWithTables_pre hp m)
    sig_post [preparePublicKeyContract, preparePublicKeySig, abi, VG.AArch64.argRegs] at post
    have cache : PreparedPublicKey p t.mem 0x10000 := post.2
    have forward := public_preparation_preserves_roots hp he (base := 1048576) (.inl rfl)
    have inverse := public_preparation_preserves_roots hp he (base := 1052480) (.inr rfl)
    exact ⟨rawVerifyConstSat p true t.mem,
      rawVerifyConstSat_pre hp true t.mem (fun i hi' => (forward i hi').trans (hf i hi'))
        (fun i hi' => (inverse i hi').trans (hi i hi')) (fun _ => cache)⟩

theorem constants_verify_entry_verified {p : Params} (hp : Ok3 p) {name : String} {code : Prog isa}
    (hv : Verified target code (verifyWithCacheContract p (abi.withConsts signRootConsts) 48))
    (hd : Message.DLe 3 code) (prepared : Bool) :
    Verified target (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name code p prepared)
      (rawVerifyK p prepared (abi.withConsts signRootConsts)) :=
  ⟨verify_entry_constants_correct hp hv.1 hd prepared,
    verify_entry_constants_ct hp hv.1 hv.2.1 prepared, raw_verify_constants_sat hp prepared⟩
end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa

theorem verify_entry_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    (name : String) (prepared : Bool) :
    Verified target
      (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
        (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
          (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) p prepared)
      (rawVerifyK p prepared (Verify.OptimizedSelected.selectedAbi)) := by
  have shared := verify_withCache_verified v p hp
  have depth := verify_withCache_dle v p
  have habi : Verify.OptimizedSelected.selectedAbi = abi.withConsts Sign.signRootConsts := rfl
  rw [habi] at shared ⊢
  exact constants_verify_entry_verified hp shared depth prepared

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlKem.AArch64 (Only)

def rawSignK (p : Params) (prepared : Bool) (A : Abi isa) : Contract isa :=
  if prepared then preparedSignContract p A 64 else signContract p A 64

def rawSignBytes (p : Params) (prepared : Bool) : Nat :=
  if prepared then preparedSecretKeyBytes p else p.skLen

def rawSignRd (p : Params) (prepared : Bool) (s : State) : List Region :=
  [⟨s.gpr .x0, rawSignBytes p prepared⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩]

def signRootRd (s : State) : List Region :=
  [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩, ⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,
    ⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]

theorem sign_entry_layout {p : Params} {prepared : Bool} {σ : State}
    (pre : (rawSignK p prepared abi).pre σ) :
    64 ≤ σ.sp.toNat ∧ σ.rd = rawSignRd p prepared σ ∧
    σ.wr = [⟨σ.gpr .x3, p.sigLen⟩, ⟨σ.gpr .x4, scratchWords p * 8⟩] ∧
    (below σ.sp 64).Disjoint ⟨σ.gpr .x0, rawSignBytes p prepared⟩ ∧
    (below σ.sp 64).Disjoint ⟨σ.gpr .x1, 64⟩ ∧
    (below σ.sp 64).Disjoint ⟨σ.gpr .x2, 32⟩ ∧
    (below σ.sp 64).Disjoint ⟨σ.gpr .x3, p.sigLen⟩ ∧
    (below σ.sp 64).Disjoint ⟨σ.gpr .x4, scratchWords p * 8⟩ := by
  cases prepared
  all_goals
    simp only [rawSignK, rawSignRd, rawSignBytes, Bool.false_eq_true, ↓reduceIte] at pre ⊢
    sig_pre [signContract, signSig, preparedSignContract, preparedSignSig,
      abi, VG.AArch64.argRegs] at pre
    obtain ⟨sp, rd, wr, _, _, _, _, _, _, _, k1, k2, k3, k4, k5, _⟩ := pre
    exact ⟨sp, rd, wr, k1, k2, k3, k4, k5⟩

theorem sign_entry_pre {p : Params} (hp : Ok3 p) {prepared : Bool} {σ s : State}
    (pre : (rawSignK p prepared abi).pre σ)
    (o : Only [.x5, .x6] (pushState .x30 σ) s)
    (h5 : s.gpr .x5 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0))
    (h6 : s.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0)) :
    (signWithCacheContract p abi 48).pre
      (s.callEntry.withRegions (signEntryRd p s) σ.wr) := by
  cases prepared
  · exact sign_empty_pre pre o (by simpa using h5) h6
  · exact sign_prepared_pre hp pre o h5 h6

theorem raw_sign_constants {p : Params} {prepared : Bool} {σ : State}
    (pre : (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre σ) :
    (rawSignK p prepared abi).pre (σ.withRegions (rawSignRd p prepared σ) σ.wr) ∧
    StaticRoots 64 σ ∧ PairedRoots 64 σ ∧ σ.rd = rawSignRd p prepared σ ++ signRootRd σ := by
  cases prepared
  all_goals
    simp only [rawSignK, Bool.false_eq_true, ↓reduceIte] at pre ⊢
    sig_pre [signContract, signSig, preparedSignContract, preparedSignSig,
      abi, VG.AArch64.argRegs, Abi.withConsts, pairedSignRootConsts_eq,
      Abi.constRegions, Abi.constsHeld, TableConstants.staticNttWords_length,
      InverseTable.expandedWords_length, PairedTable.expandedWords_length, stackBelow] at pre
    obtain ⟨sp, hd, hf, hi, hp', hff, hfw, hfs, hif, hiw, his, hpf, hpw, hps,
      hfa, hia, hpa, ht, hw, d1, d2, d3, d4, d5, d6, d7,
      k1, k2, k3, k4, k5, n1, n2, n3, n4, tail⟩ := pre
    have rd := (List.take_append_drop (σ.rd.length - 3) σ.rd).symm
    rw [ht, hd] at rd
    refine ⟨?_, ⟨⟨hf, hff, ?_, hfw, hfs, hfa⟩, ⟨hi, hif, ?_, hiw, his, hia⟩⟩,
      ⟨hp', hpf, ?_, hpw, hps, hpa⟩, rd⟩
    · sig_pre [signContract, signSig, preparedSignContract, preparedSignSig,
        abi, VG.AArch64.argRegs]
      exact ⟨sp, rfl, hw, d1, d2, d3, d4, d5, d6, d7,
        k1, k2, k3, k4, k5, n1, n2, n3, n4, tail⟩
    · apply Covers.one
      exact ⟨⟨σ.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,
        List.mem_append_left _ (by rw [rd]; simp), Region.contains_self _ _⟩
    · apply Covers.one
      exact ⟨⟨σ.syms "VG_MLDSA_INV_FOLDED",3904⟩,
        List.mem_append_left _ (by rw [rd]; simp), Region.contains_self _ _⟩
    · apply Covers.one
      exact ⟨⟨σ.syms "VG_MLDSA_INV_PAIR",4096⟩,
        List.mem_append_left _ (by rw [rd]; simp), Region.contains_self _ _⟩

theorem sign_entry_constants_pre {p : Params} (hp : Ok3 p) {prepared : Bool} {σ s : State}
    (pre : (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre σ)
    (o : Only [.x5, .x6] (pushState .x30 σ) s) (hy : s.syms = σ.syms)
    (h5 : s.gpr .x5 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0))
    (h6 : s.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0)) :
    (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre
      (s.callEntry.withRegions (signEntryRd p s ++ signRootRd s) σ.wr) := by
  have resources := raw_sign_constants pre
  have ob := operation_reset_rd o (rawSignRd p prepared σ)
  have base := sign_entry_pre hp resources.1 ob h5 h6
  have roots := operation_static_roots resources.2.1 o hy
  have pair := operation_paired_roots resources.2.2.1 o hy
  have hw : Covers σ.wr s.wr := by rw [o.wr]; exact Covers.refl _
  have borrowed : StaticRoots 48
      (s.callEntry.withRegions (signEntryRd p s ++ signRootRd s) σ.wr) :=
    ⟨operation_table_reborrow roots.forward (by simp [signRootRd]) hw,
      operation_table_reborrow roots.inverse (by simp [signRootRd]) hw⟩
  have paired : PairedRoots 48
      (s.callEntry.withRegions (signEntryRd p s ++ signRootRd s) σ.wr) :=
    operation_pair_reborrow pair (by simp [signRootRd]) hw
  apply sign_cache_pre_extend ?_ borrowed paired rfl
  simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
    signEntryRd, State.withRegions_gpr, State.withRegions_wr,
    State.callEntry_gpr _ (r := .x0) (by decide), State.callEntry_gpr _ (r := .x1) (by decide),
    State.callEntry_gpr _ (r := .x2) (by decide), State.callEntry_gpr _ (r := .x5) (by decide),
    State.callEntry_gpr _ (r := .x6) (by decide)] using base

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only)

theorem sign_entry_covers {p : Params} {prepared : Bool} {σ s : State}
    (pre : (rawSignK p prepared abi).pre σ)
    (o : Only [.x5, .x6] (pushState .x30 σ) s)
    (h5 : s.gpr .x5 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0))
    (h6 : s.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0)) :
    Covers (signEntryRd p s ++ σ.wr) (s.rd ++ s.wr) := by
  have layout := sign_entry_layout pre
  have e0 : s.gpr .x0 = σ.gpr .x0 := o.get .x0 (by decide)
  have e1 : s.gpr .x1 = σ.gpr .x1 := o.get .x1 (by decide)
  have e2 : s.gpr .x2 = σ.gpr .x2 := o.get .x2 (by decide)
  apply Covers.append
  · apply Covers.of_sub
    intro R hR
    simp only [signEntryRd, List.mem_cons, List.not_mem_nil, or_false] at hR
    rw [o.rd, show (pushState .x30 σ).rd = σ.rd from rfl, layout.2.1, rawSignRd]
    rcases hR with rfl | rfl | rfl | rfl
    · refine ⟨⟨σ.gpr .x0, rawSignBytes p prepared⟩, by simp, 0, ?_, ?_⟩
      · simpa using e0
      · cases prepared <;> simp [rawSignBytes, preparedSecretKeyBytes]
    · exact ⟨⟨σ.gpr .x1, 64⟩, by simp, 0, by simpa using e1, Nat.le_refl _⟩
    · exact ⟨⟨σ.gpr .x2, 32⟩, by simp, 0, by simpa using e2, by change 0 + 32 ≤ 32; omega_using []⟩
    · refine ⟨⟨σ.gpr .x0, rawSignBytes p prepared⟩, by simp,
        (if prepared then p.skLen else 0), h5, ?_⟩
      rw [h6]
      cases prepared
      · change 0 + (0 : BitVec 64).toNat ≤ p.skLen
        exact Nat.zero_le _
      · have hm : (BitVec.ofNat 64 (1024 * (p.ℓ + 2 * p.k))).toNat ≤ 1024 * (p.ℓ + 2 * p.k) := Nat.mod_le _ _
        simp only [rawSignBytes, ↓reduceIte, preparedSecretKeyBytes, n]
        omega_using [hm]
  · rw [o.wr]
    exact Covers.refl _

theorem sign_entry_snapshots {p : Params} (hp : Sign.Ok3 p) {prepared : Bool} {σ s : State}
    (pre : (rawSignK p prepared abi).pre σ)
    (o : Only [.x5, .x6] (pushState .x30 σ) s) :
    Spec.Sha3.bytesAt s.mem (s.gpr .x0) p.skLen = Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) p.skLen ∧
    Spec.Sha3.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) 64 ∧
    Spec.Sha3.bytesAt s.mem (s.gpr .x2) 32 = Spec.Sha3.bytesAt σ.mem (σ.gpr .x2) 32 := by
  have layout := sign_entry_layout pre
  have e0 : s.gpr .x0 = σ.gpr .x0 := o.get .x0 (by decide)
  have e1 : s.gpr .x1 = σ.gpr .x1 := o.get .x1 (by decide)
  have e2 : s.gpr .x2 = σ.gpr .x2 := o.get .x2 (by decide)
  have keySub : Region.Sub (⟨σ.gpr .x0, p.skLen⟩ : Region)
      ⟨σ.gpr .x0, rawSignBytes p prepared⟩ := Region.sub_prefix (by
    cases prepared <;> simp [rawSignBytes, preparedSecretKeyBytes])
  have keyB : p.skLen ≤ 2 ^ 64 := by rcases hp with rfl | rfl | rfl <;> decide
  have sigB : 32 ≤ 2 ^ 64 := by rcases hp with rfl | rfl | rfl <;> decide
  simp only [e0, e1, e2, o.mem]
  exact ⟨save_input_bytes (layout.2.2.2.1.sub_right keySub) keyB,
    save_input_bytes layout.2.2.2.2.1 (by decide), save_input_bytes layout.2.2.2.2.2.1 sigB⟩

theorem sign_entry_constants_covers {p : Params} {prepared : Bool} {σ s : State}
    (pre : (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre σ)
    (o : Only [.x5, .x6] (pushState .x30 σ) s) (hy : s.syms = σ.syms)
    (h5 : s.gpr .x5 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0))
    (h6 : s.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0)) :
    Covers ((signEntryRd p s ++ signRootRd s) ++ σ.wr) (s.rd ++ s.wr) := by
  have resources := raw_sign_constants pre
  have ob := operation_reset_rd o (rawSignRd p prepared σ)
  have base := sign_entry_covers resources.1 ob h5 h6
  have lift : Covers (rawSignRd p prepared σ ++ σ.wr) (s.rd ++ s.wr) := by
    rw [o.rd, o.wr]
    change Covers (rawSignRd p prepared σ ++ σ.wr) (σ.rd ++ σ.wr)
    apply Covers.append
    · apply Covers.of_mem
      intro T hT
      rw [resources.2.2.2]
      exact List.mem_append_left _ hT
    · exact Covers.refl _
  have baseRead : Covers (signEntryRd p s) (s.rd ++ s.wr) := by
    intro a n ⟨T, hT, hC⟩
    apply lift a n
    exact base a n ⟨T, List.mem_append_left _ hT, hC⟩
  have rootRead : Covers (signRootRd s) (s.rd ++ s.wr) := by
    apply Covers.left
    apply Covers.of_mem
    intro T hT
    rw [o.rd, show (pushState .x30 σ).rd = σ.rd from rfl, resources.2.2.2]
    apply List.mem_append_right
    simpa only [signRootRd, hy] using hT
  exact Covers.append_left (Covers.append_left baseRead rootRead)
    (Covers.right (by rw [o.wr]; exact Covers.refl _))

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign

theorem sign_entry_correct {p : Params} (hp : Ok3 p) {name : String}
    {code : Prog isa} (hv : ∀ σ, (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre σ →
      ∃ tr t, Exec isa code σ tr t ∧ abiPreserved σ t ∧
        (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).post σ t)
    (hd : Message.DLe 3 code) (prepared : Bool) (σ : State)
    (pre : (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name code p prepared) σ tr t ∧
      abiPreserved σ t ∧ (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).post σ t := by
  have resources := raw_sign_constants pre
  have layout := sign_entry_layout resources.1
  have depth := (operation_call_bounds hd).1
  have guard : ∀ R ∈ σ.wr, (below σ.sp 16).Disjoint R := by
    intro R hR
    have wr : σ.wr = [⟨σ.gpr .x3, p.sigLen⟩, ⟨σ.gpr .x4, scratchWords p * 8⟩] := layout.2.2.1
    rw [wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact layout.2.2.2.2.2.2.1.sub_left (below_sub (by decide) (by decide))
    · exact layout.2.2.2.2.2.2.2.sub_left (below_sub (by decide) (by decide))
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name code p prepared) σ
      fun t => abiPreserved σ t ∧ (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).post σ t := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Sign.entry
    refine WP.frameReg (Nat.le_trans (by decide) layout.1) guard ?_ (by
      simpa only [Code.aarch64Depth, Nat.zero_max] using depth)
    change WP isa (.seq (.block (operationSetup p true prepared)) (.call name code)) (pushState .x30 σ) _
    refine WP.seq (WP.mono_syms (operationSetup_ok p true prepared (pushState .x30 σ)) fun s hs sy => ?_)
    have hc := sign_entry_constants_covers pre hs.1 sy hs.2.1 hs.2.2
    have hcpre := sign_entry_constants_pre hp pre hs.1 sy hs.2.1 hs.2.2
    have hw : Covers σ.wr s.wr := by rw [hs.1.wr]; exact Covers.refl _
    refine WP.callFV hv hcpre hc hw (fun t hr ht hsp hf hcs hvs post => ?_) (operation_call_bounds hd).2
    refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
    · intro r hR
      by_cases h30 : r = .x30
      · subst r; simp [State.write]
      simp only [State.write, h30, ite_false]
      rw [hcs r hR h30, hs.1.get r (by revert hR h30; cases r <;> decide)]
      rfl
    · intro r hR
      exact (hvs r hR).trans (hs.1.vcs r hR)
    · have ob := operation_reset_rd hs.1 (rawSignRd p prepared σ)
      have snaps := sign_entry_snapshots hp resources.1 ob
      have sk : Spec.Sha3.bytesAt s.mem (s.gpr .x0) p.skLen = Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) p.skLen := snaps.1
      have mu : Spec.Sha3.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) 64 := snaps.2.1
      have rnd : Spec.Sha3.bytesAt s.mem (s.gpr .x2) 32 = Spec.Sha3.bytesAt σ.mem (σ.gpr .x2) 32 := snaps.2.2
      have e3 : s.gpr .x3 = σ.gpr .x3 := hs.1.get .x3 (by decide)
      sig_post [signWithCacheContract, signWithCacheSig, signSig, abi, VG.AArch64.argRegs, Abi.withConsts] at post
      rw [sk, mu, rnd, e3] at post
      cases prepared
      all_goals
        simp only [rawSignK, Bool.false_eq_true, ↓reduceIte]
        sig_post [signContract, signSig, preparedSignContract, preparedSignSig,
          abi, VG.AArch64.argRegs, Abi.withConsts]
        simpa only [State.write, reduceCtorEq, ite_false] using post
  obtain ⟨tr, t, he, habi, hpost⟩ := main
  exact ⟨tr, t, he, habi, hpost⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only)

theorem sign_entry_base_pub {p : Params} (hp : Ok3 p) {prepared : Bool} {σ τ x y : State}
    (px : (rawSignK p prepared abi).pre σ) (py : (rawSignK p prepared abi).pre τ)
    (pub : (rawSignK p prepared abi).pub σ τ)
    (ox : Only [.x5, .x6] (pushState .x30 σ) x)
    (oy : Only [.x5, .x6] (pushState .x30 τ) y)
    (x5 : x.gpr .x5 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0))
    (x6 : x.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0))
    (y5 : y.gpr .x5 = τ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0))
    (y6 : y.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0))
    (dx : x.dit = σ.dit) (dy : y.dit = τ.dit) :
    (signWithCacheContract p abi 48).pub
      (x.callEntry.withRegions (signEntryRd p x) σ.wr)
      (y.callEntry.withRegions (signEntryRd p y) τ.wr) := by
  have hd : σ.dit = τ.dit := by
    cases prepared
    all_goals
      simp only [rawSignK, Bool.false_eq_true, ↓reduceIte] at pub
      sig_pub_keep [signContract, signSig, preparedSignContract, preparedSignSig, abi,
        VG.AArch64.argRegs] at pub
      exact pub.2.1
  have snapsX := sign_entry_snapshots hp px ox
  have snapsY := sign_entry_snapshots hp py oy
  have base : σ.sp = τ.sp ∧
      signLeak p (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) p.skLen)
        (Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) 64) (Spec.Sha3.bytesAt σ.mem (σ.gpr .x2) 32) =
      signLeak p (Spec.Sha3.bytesAt τ.mem (τ.gpr .x0) p.skLen)
        (Spec.Sha3.bytesAt τ.mem (τ.gpr .x1) 64) (Spec.Sha3.bytesAt τ.mem (τ.gpr .x2) 32) ∧
      σ.gpr .x0 = τ.gpr .x0 ∧ σ.gpr .x1 = τ.gpr .x1 ∧ σ.gpr .x2 = τ.gpr .x2 ∧
      σ.gpr .x3 = τ.gpr .x3 ∧ σ.gpr .x4 = τ.gpr .x4 := by
    cases prepared
    all_goals
      simp only [rawSignK, Bool.false_eq_true, ↓reduceIte] at pub
      sig_pub [signContract, signSig, preparedSignContract, preparedSignSig, abi, VG.AArch64.argRegs] at pub
      exact pub
  sig_pub [signWithCacheContract, signWithCacheSig, signSig, abi, VG.AArch64.argRegs]
  refine ⟨?_, dx.trans (hd.trans dy.symm), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ox.sp, oy.sp]
    exact congrArg (· - 16) base.1
  · rw [snapsX.1, snapsX.2.1, snapsX.2.2, snapsY.1, snapsY.2.1, snapsY.2.2]
    exact base.2.1
  · exact (ox.get .x0 (by decide)).trans (base.2.2.1.trans (oy.get .x0 (by decide)).symm)
  · exact (ox.get .x1 (by decide)).trans (base.2.2.2.1.trans (oy.get .x1 (by decide)).symm)
  · exact (ox.get .x2 (by decide)).trans (base.2.2.2.2.1.trans (oy.get .x2 (by decide)).symm)
  · exact (ox.get .x3 (by decide)).trans (base.2.2.2.2.2.1.trans (oy.get .x3 (by decide)).symm)
  · exact (ox.get .x4 (by decide)).trans (base.2.2.2.2.2.2.trans (oy.get .x4 (by decide)).symm)
  · rw [x5, y5, base.2.2.1]
  · rw [x6, y6]

theorem raw_sign_constants_pub {p : Params} {prepared : Bool} {x y : State}
    (h : (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pub x y) :
    (rawSignK p prepared abi).pub
      (x.withRegions (rawSignRd p prepared x) x.wr)
      (y.withRegions (rawSignRd p prepared y) y.wr) ∧
    x.syms "VG_MLDSA_NTT_EXPANDED" = y.syms "VG_MLDSA_NTT_EXPANDED" ∧
    x.syms "VG_MLDSA_INV_FOLDED" = y.syms "VG_MLDSA_INV_FOLDED" ∧
    x.syms "VG_MLDSA_INV_PAIR" = y.syms "VG_MLDSA_INV_PAIR" := by
  cases prepared
  all_goals
    simp only [rawSignK, Bool.false_eq_true, ↓reduceIte] at h ⊢
    sig_pub_keep [signContract, signSig, preparedSignContract, preparedSignSig,
      abi, VG.AArch64.argRegs, Abi.withConsts, pairedSignRootConsts_eq] at h
    obtain ⟨sp, hd, hf, hi, hp', leak, h0, h1, h2, h3, h4⟩ := h
    refine ⟨?_, hf, hi, hp'⟩
    sig_pub [signContract, signSig, preparedSignContract, preparedSignSig,
      abi, VG.AArch64.argRegs]
    exact ⟨sp, hd, leak, h0, h1, h2, h3, h4⟩

theorem sign_entry_pub {p : Params} (hp : Ok3 p) {prepared : Bool} {σ τ x y : State}
    (px : (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre σ)
    (py : (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre τ)
    (pub : (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pub σ τ)
    (ox : Only [.x5, .x6] (pushState .x30 σ) x)
    (oy : Only [.x5, .x6] (pushState .x30 τ) y)
    (sx : x.syms = σ.syms) (sy : y.syms = τ.syms)
    (x5 : x.gpr .x5 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0))
    (x6 : x.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0))
    (y5 : y.gpr .x5 = τ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0))
    (y6 : y.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0))
    (dx : x.dit = σ.dit) (dy : y.dit = τ.dit) :
    (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pub
      (x.callEntry.withRegions (signEntryRd p x ++ signRootRd x) σ.wr)
      (y.callEntry.withRegions (signEntryRd p y ++ signRootRd y) τ.wr) := by
  have pub0 := raw_sign_constants_pub pub
  have base := sign_entry_base_pub hp (raw_sign_constants px).1 (raw_sign_constants py).1
    pub0.1 (operation_reset_rd ox _) (operation_reset_rd oy _) x5 x6 y5 y6 dx dy
  sig_pub_keep [signWithCacheContract, signWithCacheSig, signSig, abi, VG.AArch64.argRegs] at base
  sig_pub [signWithCacheContract, signWithCacheSig, signSig, abi, VG.AArch64.argRegs,
    Abi.withConsts, pairedSignRootConsts_eq]
  obtain ⟨sp, hd, leak, h0, h1, h2, h3, h4, h5, h6⟩ := base
  exact ⟨sp, hd, by simpa only [sx, sy] using pub0.2.1,
    by simpa only [sx, sy] using pub0.2.2.1, by simpa only [sx, sy] using pub0.2.2.2,
    leak, h0, h1, h2, h3, h4, h5, h6⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only)

theorem sign_entry_bases {p : Params} {prepared : Bool} {x y : State}
    (h : (rawSignK p prepared abi).pub x y) : SameIn [.x0] x y := by
  cases prepared
  all_goals
    simp only [rawSignK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pub [signContract, signSig, preparedSignContract, preparedSignSig,
      abi, VG.AArch64.argRegs] at h
    exact ⟨fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.2.2.1, h.1⟩

def RawSignEntryRel (p : Params) (prepared : Bool) (x y : State) : Prop :=
  (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre x ∧
  (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre y ∧
  (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pub x y

def SignEntryCallRel (p : Params) (prepared : Bool) (x y : State) : Prop :=
  ∃ σ τ, RawSignEntryRel p prepared σ τ ∧
    Only [.x5, .x6] (pushed .x30 σ) x ∧ Only [.x5, .x6] (pushed .x30 τ) y ∧
    x.gpr .x5 = σ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0) ∧
    x.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0) ∧
    y.gpr .x5 = τ.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0) ∧
    y.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0) ∧
    x.syms = σ.syms ∧ y.syms = τ.syms ∧ x.dit = σ.dit ∧ y.dit = τ.dit

def SignEntrySetupOut (p : Params) (prepared : Bool) (s t : State) : Prop :=
  (Only [.x5, .x6] s t ∧
    t.gpr .x5 = s.gpr .x0 + BitVec.ofNat 64 (if prepared then p.skLen else 0) ∧
    t.gpr .x6 = BitVec.ofNat 64 (if prepared then 1024 * (p.ℓ + 2 * p.k) else 0)) ∧ t.syms = s.syms

theorem sign_entry_setup_syms_ok (p : Params) (prepared : Bool) (s : State) :
    WP isa (.block (operationSetup p true prepared)) s (SignEntrySetupOut p prepared s) := by
  exact WP.mono_syms (operationSetup_ok p true prepared s) (fun _ h hy => ⟨h, hy⟩)

theorem sign_entry_ct {p : Params} (hp : Ok3 p) {name : String} {code : Prog isa}
    (hv : ∀ σ, (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre σ →
      ∃ tr t, Exec isa code σ tr t ∧ abiPreserved σ t ∧
        (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).post σ t)
    (hct : ConstantTime isa (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre
      (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pub code) (prepared : Bool) :
    ConstantTime isa (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre
      (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pub
      (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name code p prepared) := by
  have hs : ∀ x y, RawSignEntryRel p prepared x y → x.sp = y.sp :=
    fun _ _ h => (sign_entry_bases (raw_sign_constants_pub h.2.2).1).2
  have trace : RelCT isa (RawSignEntryRel p prepared)
      (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name code p prepared) (fun _ _ => True) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Sign.entry
    refine frame_tr (R := fun _ _ => True) hs ?_
    change RelCT isa (PushRel .x30 (RawSignEntryRel p prepared))
      (.seq (.block (operationSetup p true prepared)) (.call name code)) (fun _ _ => True)
    refine RelCT.seq (R := SignEntryCallRel p prepared) (RelCT.postDep
      (RelCT.mono (operationSetup_tr hp true prepared) (fun x y h => ?_) (fun _ _ _ => trivial))
      (fun x y _ => ⟨WP.dit (operationSetup_noWriteDit _ _ _) (sign_entry_setup_syms_ok p prepared x),
        WP.dit (operationSetup_noWriteDit _ _ _) (sign_entry_setup_syms_ok p prepared y)⟩)
      (fun x y x' y' h hx hy => ?_)) ?_
    · rcases h with ⟨σ, τ, h, rfl, rfl⟩
      exact ⟨(sign_entry_bases (raw_sign_constants_pub h.2.2).1).1,
        congrArg (· - 16) (hs σ τ h)⟩
    · rcases h with ⟨σ, τ, h, rfl, rfl⟩
      exact ⟨σ, τ, h, hx.1.1.1, hy.1.1.1, hx.1.1.2.1, hx.1.1.2.2,
        hy.1.1.2.1, hy.1.1.2.2, hx.1.2, hy.1.2, hx.2, hy.2⟩
    · apply RelCT.callEx hv hct
      rintro x y ⟨σ, τ, h, ox, oy, x5, x6, y5, y6, sx, sy, dx, dy⟩
      have nx := operation_narrow ox
      have ny := operation_narrow oy
      refine ⟨signEntryRd p x ++ signRootRd x, σ.wr,
        signEntryRd p y ++ signRootRd y, τ.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have px := sign_entry_constants_pre hp h.1 nx sx x5 x6
        simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
          signEntryRd, signRootRd, State.withRegions_gpr, operation_region_syms] using px
      · have py := sign_entry_constants_pre hp h.2.1 ny sy y5 y6
        simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
          signEntryRd, signRootRd, State.withRegions_gpr, operation_region_syms] using py
      · have pub := sign_entry_pub hp h.1 h.2.1 h.2.2 nx ny sx sy x5 x6 y5 y6 dx dy
        simpa only [State.callEntry_withRegions, State.withRegions_withRegions,
          signEntryRd, signRootRd, State.withRegions_gpr, operation_region_syms] using pub
      · have cover := sign_entry_constants_covers h.1 nx sx x5 x6
        change Covers ((signEntryRd p x ++ signRootRd x) ++ σ.wr) (σ.rd ++ σ.wr) at cover
        exact cover.trans (operation_cover ox)
      · rw [ox.wr]; exact push_wr_cover .x30 σ
      · have cover := sign_entry_constants_covers h.2.1 ny sy y5 y6
        change Covers ((signEntryRd p y ++ signRootRd y) ++ τ.wr) (τ.rd ++ τ.wr) at cover
        exact cover.trans (operation_cover oy)
      · rw [oy.wr]; exact push_wr_cover .x30 τ
  intro x y tx ty x' y' hx hy hpub ex ey
  exact (trace x y tx ty x' y' ⟨hx, hy, hpub⟩ ex ey).1

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## Prepared signing entries have satisfiable layouts -/

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

def prepSecretWithTables (p : Params) (m : Mem) : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x10000 | .x2 => 0x200000 | _ => 0
  sp := 0x1000000
  mem := m
  rd := [⟨0x1000, p.skLen⟩]
  wr := [⟨0x10000, preparedSecretKeyBytes p⟩, ⟨0x200000,1024⟩]

theorem prepSecretWithTables_pre {p : Params} (hp : Ok3 p) (m : Mem) :
    (prepareSecretKeyContract p abi 80).pre (prepSecretWithTables p m) := by
  rcases hp with rfl | rfl | rfl
  all_goals
    sig_pre [prepareSecretKeyContract, prepareSecretKeySig, abi, VG.AArch64.argRegs]
    sig_and_intros
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide +kernel

theorem prepare_secret_depth {p : Params} (hp : Ok3 p) :
    (Impl.MlDsa.AArch64.PreparedKey.prepareSecret p).aarch64Depth ≤ 5 := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem secret_preparation_preserves_roots {p : Params} (hp : Ok3 p) {m : Mem} {t : State}
    {tr : List Leak}
    (he : Exec isa (Impl.MlDsa.AArch64.PreparedKey.prepareSecret p) (prepSecretWithTables p m) tr t)
    {base : Addr} (hb : base = 1048576 ∨ base = 1052480 ∨ base = 1056384) :
    ∀ i < 512, t.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
      m.readW (base + BitVec.ofNat 64 (8 * i)) 64 := by
  have depth := prepare_secret_depth hp
  have bound : 16 * (Impl.MlDsa.AArch64.PreparedKey.prepareSecret p).aarch64Depth < 2 ^ 64 := by omega_using [depth]
  have frame := Exec.frameSp he bound
  intro i hi
  apply frame.readW (r := ⟨base,4096⟩)
    (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) ?_ (by decide)
  intro R hR
  simp only [prepSecretWithTables, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · rcases hp with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals exact Region.disjoint_of_sep (by decide)
  · rcases hb with rfl | rfl | rfl
    all_goals exact Region.disjoint_of_sep (by decide)
  · have hs : Region.Sub (below (0x1000000 : Addr)
        (16 * (Impl.MlDsa.AArch64.PreparedKey.prepareSecret p).aarch64Depth))
        (below (0x1000000 : Addr) 80) := below_sub (by omega_using [depth]) (by decide)
    apply Region.Disjoint.sub_right _ hs
    rcases hb with rfl | rfl | rfl
    all_goals exact Region.disjoint_of_sep (by decide)

def rawSignSat (p : Params) (prepared : Bool) (m : Mem) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x2 => 0x30000 | .x3 => 0x40000 | .x4 => 0x400000 | _ => 0
  sp := 0x1000000
  mem := m
  rd := [⟨0x10000, rawSignBytes p prepared⟩, ⟨0x20000,64⟩, ⟨0x30000,32⟩]
  wr := [⟨0x40000,p.sigLen⟩,⟨0x400000,scratchWords p * 8⟩]

theorem raw_sign_sat_pre {p : Params} (hp : Ok3 p) {m : Mem}
    (prepared : Bool) (cache : prepared = true → PreparedSecretKey p m 0x10000) :
    (rawSignK p prepared abi).pre (rawSignSat p prepared m) := by
  cases prepared
  · rcases hp with rfl | rfl | rfl
    all_goals
      simp only [rawSignK, Bool.false_eq_true, ↓reduceIte]
      sig_pre [signContract, signSig, abi, VG.AArch64.argRegs]
      simp only [rawSignBytes, Bool.false_eq_true, ↓reduceIte]
      sig_and_intros
      all_goals first | exact Region.disjoint_of_sep (by decide) | decide +kernel
  · have cached := cache rfl
    rcases hp with rfl | rfl | rfl
    all_goals
      simp only [rawSignK, ↓reduceIte]
      sig_pre [preparedSignContract, preparedSignSig, abi, VG.AArch64.argRegs]
      simp only [rawSignBytes, ↓reduceIte]
      sig_and_intros
      all_goals first | exact cached | exact Region.disjoint_of_sep (by decide) | decide +kernel

theorem raw_sign_pre_extend {p : Params} {prepared : Bool} {s : State}
    (h : (rawSignK p prepared abi).pre (s.withRegions (rawSignRd p prepared s) s.wr))
    (hr : StaticRoots 64 s) (rp : PairedRoots 64 s)
    (hd : s.rd = rawSignRd p prepared s ++ signRootRd s) :
    (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s := by
  cases prepared
  all_goals
    simp only [rawSignK, Bool.false_eq_true, ↓reduceIte] at h ⊢
    sig_pre [signContract, signSig, preparedSignContract, preparedSignSig,
      abi, VG.AArch64.argRegs] at h
    sig_pre [signContract, signSig, preparedSignContract, preparedSignSig,
      abi, VG.AArch64.argRegs, Abi.withConsts, pairedSignRootConsts_eq,
      Abi.constRegions, Abi.constsHeld, TableConstants.staticNttWords_length,
      InverseTable.expandedWords_length, PairedTable.expandedWords_length, stackBelow]
    obtain ⟨sp, _rd, wr, d1, d2, d3, d4, d5, d6, d7,
      k1, k2, k3, k4, k5, n1, n2, n3, n4, tail⟩ := h
    exact ⟨sp,by rw [hd]; rfl,hr.forward.held,hr.inverse.held,rp.held,
      hr.forward.fit,hr.forward.writable,hr.forward.stack,hr.inverse.fit,
      hr.inverse.writable,hr.inverse.stack,rp.fit,rp.writable,rp.stack,
      hr.forward.aligned,hr.inverse.aligned,rp.aligned,by rw [hd]; rfl,
      wr,d1,d2,d3,d4,d5,d6,d7,k1,k2,k3,k4,k5,n1,n2,n3,n4,tail⟩

def rawSignConstSat (p : Params) (prepared : Bool) (m : Mem) : State :=
  { rawSignSat p prepared m with
    syms := fun name => if name = "VG_MLDSA_NTT_EXPANDED" then 1048576 else
      if name = "VG_MLDSA_INV_FOLDED" then 1052480 else 1056384
    rd := (rawSignSat p prepared m).rd ++ [⟨1048576,3904⟩,⟨1052480,3904⟩,⟨1056384,4096⟩] }

theorem rawSignConstSat_roots (p : Params) (hp : Ok3 p) (prepared : Bool) (m : Mem)
    (hf : ∀ i < 488, m.readW (1048576 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0)
    (hi : ∀ i < 488, m.readW (1052480 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (hp' : ∀ i < 512, m.readW (1056384 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD i 0) :
    StaticRoots 64 (rawSignConstSat p prepared m) ∧ PairedRoots 64 (rawSignConstSat p prepared m) := by
  have forward : StaticTable 64 "VG_MLDSA_NTT_EXPANDED"
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords (rawSignConstSat p prepared m) := by
    refine ⟨hf, by dsimp [rawSignConstSat]; decide, ?_, ?_,
      by apply Region.disjoint_of_sep; dsimp [rawSignConstSat,rawSignSat]; decide,
      by rw [show (rawSignConstSat p prepared m).syms "VG_MLDSA_NTT_EXPANDED" = 1048576 from rfl]; decide⟩
    · exact Covers.one ⟨⟨1048576,3904⟩, by simp [rawSignConstSat], Region.contains_self _ _⟩
    · rcases hp with rfl | rfl | rfl
      all_goals
        simp only [rawSignConstSat,rawSignSat,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
        exact ⟨Region.disjoint_of_sep (by decide),Region.disjoint_of_sep (by decide)⟩
  have inverse : StaticTable 64 "VG_MLDSA_INV_FOLDED"
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords (rawSignConstSat p prepared m) := by
    refine ⟨hi, by dsimp [rawSignConstSat]; decide, ?_, ?_,
      by apply Region.disjoint_of_sep; dsimp [rawSignConstSat,rawSignSat]; decide,
      by rw [show (rawSignConstSat p prepared m).syms "VG_MLDSA_INV_FOLDED" = 1052480 from rfl]; decide⟩
    · exact Covers.one ⟨⟨1052480,3904⟩, by simp [rawSignConstSat], Region.contains_self _ _⟩
    · rcases hp with rfl | rfl | rfl
      all_goals
        simp only [rawSignConstSat,rawSignSat,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
        exact ⟨Region.disjoint_of_sep (by decide),Region.disjoint_of_sep (by decide)⟩
  have pair : PairedRoots 64 (rawSignConstSat p prepared m) := by
    refine ⟨hp', by dsimp [rawSignConstSat]; decide, ?_, ?_,
      by apply Region.disjoint_of_sep; dsimp [rawSignConstSat,rawSignSat]; decide,
      by rw [show (rawSignConstSat p prepared m).syms "VG_MLDSA_INV_PAIR" = 1056384 from rfl]; decide⟩
    · exact Covers.one ⟨⟨1056384,4096⟩, by simp [rawSignConstSat], Region.contains_self _ _⟩
    · rcases hp with rfl | rfl | rfl
      all_goals
        simp only [rawSignConstSat,rawSignSat,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
        exact ⟨Region.disjoint_of_sep (by decide),Region.disjoint_of_sep (by decide)⟩
  exact ⟨⟨forward,inverse⟩,pair⟩

theorem rawSignConstSat_pre {p : Params} (hp : Ok3 p) (prepared : Bool) (m : Mem)
    (hf : ∀ i < 488, m.readW (1048576 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0)
    (hi : ∀ i < 488, m.readW (1052480 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (hp' : ∀ i < 512, m.readW (1056384 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD i 0)
    (cache : prepared = true → PreparedSecretKey p m 0x10000) :
    (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre
      (rawSignConstSat p prepared m) := by
  have roots := rawSignConstSat_roots p hp prepared m hf hi hp'
  apply raw_sign_pre_extend ?_ roots.1 roots.2 rfl
  have base := raw_sign_sat_pre hp prepared cache
  cases prepared
  all_goals
    simp only [rawSignK,Bool.false_eq_true,↓reduceIte] at base ⊢
    sig_pre [signContract,signSig,preparedSignContract,preparedSignSig,
      abi,VG.AArch64.argRegs] at base ⊢
    exact base

theorem raw_sign_sat {p : Params} (hp : Ok3 p) (prepared : Bool) :
    ∃ s, (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s := by
  have roots := pairedRoots_entry (by decide) (pairedSign_sat hp)
  let m := (pairedSignSat p).mem
  have hf : ∀ i < 488, m.readW (1048576 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0 := roots.2.1.forward.held
  have hi : ∀ i < 488, m.readW (1052480 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0 := roots.2.1.inverse.held
  have hp' : ∀ i < 512, m.readW (1056384 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD i 0 := roots.2.2.held
  cases prepared
  · exact ⟨rawSignConstSat p false m,
      rawSignConstSat_pre hp false m hf hi hp' (by intro h; cases h)⟩
  · obtain ⟨_,t,he,_,post⟩ := secret_correct hp (prepSecretWithTables p m) (prepSecretWithTables_pre hp m)
    sig_post [prepareSecretKeyContract,prepareSecretKeySig,abi,VG.AArch64.argRegs] at post
    have cache : PreparedSecretKey p t.mem 0x10000 := post.2
    have forward := secret_preparation_preserves_roots hp he (base := 1048576) (.inl rfl)
    have inverse := secret_preparation_preserves_roots hp he (base := 1052480) (.inr (.inl rfl))
    have pair := secret_preparation_preserves_roots hp he (base := 1056384) (.inr (.inr rfl))
    exact ⟨rawSignConstSat p true t.mem,
      rawSignConstSat_pre hp true t.mem
        (fun i hi' => (forward i (by omega_using [hi'])).trans (hf i hi'))
        (fun i hi' => (inverse i (by omega_using [hi'])).trans (hi i hi'))
        (fun i hi' => (pair i hi').trans (hp' i hi')) (fun _ => cache)⟩

theorem sign_entry_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    (name : String) (prepared : Bool) :
    Verified target
      (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
        (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p) p prepared)
      (rawSignK p prepared (abi.withConsts pairedSignRootConsts)) :=
  ⟨sign_entry_correct hp (withCache_verified v p hp).1 (sign_withCache_dle v hp) prepared,
    sign_entry_ct hp (withCache_verified v p hp).1 (withCache_verified v p hp).2.1 prepared,
    raw_sign_sat hp prepared⟩
end VG.Proof.MlDsa.AArch64.PreparedKey
