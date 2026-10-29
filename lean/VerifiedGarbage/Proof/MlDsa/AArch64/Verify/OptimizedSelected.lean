module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyCallPre
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedTop

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Final
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Optimized
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedState
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedHintPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedDot
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedTimingBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedNttTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedNtt
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSingleCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowReady
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotCallTiming
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedPiece
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Lay
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSat
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRel
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifySat
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifySat
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyCorrect

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedRow.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen

/-- All arithmetic uses the same Montgomery factor until the inverse removes
it; packed output is identical to the canonical verification algorithm. -/
theorem row_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A' : Nat→Nat→Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.row P p r) s (SC p S σ h A' c0 q p.ℓ true (r+1)) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.row
  refine WP.seq (WP.mono (dot_ok hF hp hr hs) fun s ⟨hs,hw⟩=>?_)
  refine WP.seq (WP.mono (unpack_ok hP hF hp hr hs hw) fun s ⟨hs,hw,ht⟩=>?_)
  refine WP.seq (WP.mono (nttT_ok hF hp hr hs hw ht) fun s ⟨hs,hw,ht⟩=>?_)
  refine WP.seq (WP.mono (product_ok hF hp hr hs hw ht) fun s ⟨hs,hw,ht⟩=>?_)
  refine WP.seq (WP.mono (subtract_ok hF hp hr hs hw ht) fun s ⟨hs,hw⟩=>?_)
  refine WP.seq (WP.mono (inverse_ok hF hp hr hs hw) fun s ⟨hs,hw⟩=>?_)
  exact hintPack_ok hF hp hr hs hw

end VG.Proof.MlDsa.AArch64.Verify.Optimized
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

theorem rows_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) (hs : SCx p S p.ℓ true 0 σ s) :
    WP isa (seqR (Impl.MlDsa.AArch64.Verify.Optimized.row P p) 0 p.k) s
      (SCx p S p.ℓ true p.k σ) := by
  simpa only [Nat.zero_add] using seqR_ok (I:=fun r=>SCx p S p.ℓ true r σ) p.k 0
    (fun r _ hr s ⟨h,A,c,q,hs⟩=>WP.mono (row_ok hP hF hp (by omega) hs)
      fun t ht=>⟨h,A,c,q,ht⟩) s hs

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
    CalleeOk.of_verified hS AddSub.sub_verified (Nat.zero_le _) (by change 0≤S;omega)
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

theorem row_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (SCx p S p.ℓ true r)) (Impl.MlDsa.AArch64.Verify.Optimized.row P p r)
      (RootPair p S (SCx p S p.ℓ true (r+1))) := by
  exact (dot_tr hF hr).seq ((unpack_tr hP hF hr).seq ((nttT_tr hF hr).seq
    ((product_tr hF hr).seq ((subtract_tr hF hP.s64 hr).seq
      ((inverse_tr hF hr).seq (hintPack_tr hF hr))))))
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedCompute.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.KeyGen
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem compute_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    Piece p S (fun σ s=>VB p σ s ∧ Sign.StaticRoots S s) (VFin p)
      (Impl.MlDsa.AArch64.Verify.Optimized.computeWith keccak.callee P p) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.computeWith
  refine Piece.seq (J:=SCx p S p.ℓ false 0) ?_ (Piece.seq (J:=SCx p S p.ℓ true 0) ?_
    (Piece.seq (J:=SCx p S p.ℓ true p.k) ?_ (Piece.of_vpiece (finish_vpiece hP.s16 hP.s64 hF))))
  · refine ⟨fun σ s hp hs=>nttZ_vector_ok hF hp (vb_sc hs.1 hs.2),?_⟩
    exact (nttZ_vector_tr hF).mono
      (fun _ _ ⟨⟨σ,τ,hσ,hτ,pub,ix,iy⟩,et⟩=>⟨⟨σ,τ,hσ,hτ,pub,vb_sc ix.1 ix.2,vb_sc iy.1 iy.2⟩,et⟩)
      (fun _ _ _=>trivial)
  · refine ⟨fun σ s hp ⟨h,A,c,q,hs⟩=>WP.mono (nttC_ok hF hp hs) fun t ht=>⟨h,A,c,q,ht⟩,?_⟩
    exact (nttC_tr hF).mono (fun _ _ h=>h) (fun _ _ _=>trivial)
  · refine ⟨fun σ s hp hs=>rows_ok hP hF hp hs,?_⟩
    have ht := seqR_tr (Q:=fun r=>RootPair p S (SCx p S p.ℓ true r)) p.k 0
      fun r _ hr=>row_tr hP hF (by omega)
    exact ht.mono (fun _ _ h=>h) (fun _ _ _=>trivial)

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
  have hh : DLe (S/16) P.hintUnpack := ⟨by have:=hP.hintUnpack.fd;omega⟩
  have hd : DLe (S/16) (hint P p) := by unfold hint;dle_tac
  have := hd.le;omega

theorem zOne_depth {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) (i : Nat) :
    16*(zOne P p i).aarch64Depth≤S := by
  have hb : DLe (S/16) P.bitUnpack := ⟨by have:=hP.bitUnpack.fd;omega⟩
  have hn : DLe (S/16) P.normLt := ⟨by have:=hP.normLt.fd;omega⟩
  have hd : DLe (S/16) (zOne P p i) := by unfold zOne;dle_tac
  have := hd.le;omega

theorem body_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    Piece p S (fun σ s=>(VC p σ s ∧ s.gpr .x24=1) ∧ Sign.StaticRoots S s) (VFin p)
      (Impl.MlDsa.AArch64.Verify.Optimized.bodyWith keccak.callee P p) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.bodyWith
  refine (Piece.of_vpiece (OptimizedSamples.rooted_piece (hint_vpiece hP hF) (hint_depth hP p) hP.s64)).seq
    (Piece.ifOk (T:=fun σ=>(hintOf p σ).isSome=true) (fun _ _ _ h=>h.1.2.1)
      (fun _ _ _ _ pub=>by rw [hintOf,hintOf,(vPub_eq pub).2.2.2.1]) ?_ ?_)
  · refine Piece.seq (J:=fun σ s=>Z0 p p.ℓ σ s ∧ Sign.StaticRoots S s) ?_
      (Piece.ifOk (T:=fun σ=>normOk p σ p.ℓ) (fun _ _ _ h=>h.1.2)
        (fun _ _ _ _ pub=>by simp only [normOk,zOf,(vPub_eq pub).2.2.2.1]) ?_ ?_)
    · refine Piece.mono (Piece.seqR (I:=fun j σ s=>Z0 p j σ s ∧ Sign.StaticRoots S s) p.ℓ 0
        fun j _ hj=>Piece.of_vpiece (OptimizedSamples.rooted_piece (zOne_vpiece hP hF (by omega))
          (zOne_depth hP p j) hP.s64)) ?_ ?_
      · intro σ s _ ⟨⟨⟨hv,hx,hH⟩,roots⟩,ht⟩
        refine ⟨⟨⟨hv,?_,fun _ h=>absurd h (Nat.not_lt_zero _)⟩,?_⟩,roots⟩
        · obtain ⟨hh,e⟩:=Option.isSome_iff_exists.mp ht
          exact ⟨hh,e,hH hh e⟩
        · rw [hx];exact flag_congr (iff_of_true ht (normOk_zero p σ))
      · intro _ _ _ h;simpa only [Nat.zero_add] using h
    · refine (Piece.of_vpiece (OptimizedSamples.samples_rooted_vpiece hP hF)).seq (compute_piece hP hF) |>.mono ?_ (fun _ _ _ h=>h)
      intro _ _ _ ⟨⟨hz,roots⟩,hn⟩
      exact ⟨⟨hz,hn⟩,roots⟩
    · intro σ s _ ⟨h,roots⟩ hn
      refine ⟨h.1.vc,.inr ⟨by rw [h.2];exact ifn hn _ _,?_⟩⟩
      obtain ⟨hh,e,_⟩:=h.1.hint
      exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e
        (by rw [Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1];exact hn)
  · intro σ s _ ⟨h,roots⟩ hn
    refine ⟨h.1,.inr ⟨by rw [h.2.1];exact ifn hn _ _,?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ (Option.not_isSome_iff_eq_none.mp hn)]
    nofun

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedPre.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized

def rootRegions (s : State) : List Region :=
  [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩]

theorem entry {p : Params} {S : Nat} {s : State} (hS : 0<S)
    (h : (verifyContract p (abi.withConsts signRootConsts) S).pre s) :
    vPre p S s ∧ StaticRoots S s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  sig_pre [verifyContract,verifySig,abi,argRegs,Abi.withConsts,Sign.signRootConsts_eq,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,
    InverseTable.expandedWords_length,stackBelow,List.range,List.range.loop] at h
  obtain ⟨hsp,hd,hf,hi,hff,hfw,hfs,hif,hiw,his,hfa,hia,ht,hw,d1,d2,d3,
    k1,k2,k3,k4,n1,n2,n3,n4⟩ := h
  have hrd : s.rd=vInputs p s++rootRegions s := by
    rw [←List.take_append_drop (s.rd.length-2) s.rd,ht,hd]
    rfl
  refine ⟨⟨?_,fun r hr=>by rw [hrd]; exact List.mem_append_left _ hr⟩,
    ⟨⟨hf,hff,?_,hfw,?_,hfa⟩,⟨hi,hif,?_,hiw,?_,hia⟩⟩⟩
  · sig_pre [verifyContract,verifySig,abi,argRegs,List.range,List.range.loop]
    exact ⟨hsp,rfl,hw,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,n4⟩
  · apply Covers.one
    exact ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,by rw [hrd]; simp [rootRegions],Region.contains_self _ _⟩
  · exact hfs
  · apply Covers.one
    exact ⟨⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,by rw [hrd]; simp [rootRegions],Region.contains_self _ _⟩
  · exact his

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedContract.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (Ok3 StaticRoots RootSymbolsEq signRootConsts)

/-- Internal proof boundary retains the original verifier semantics and adds
only the immutable transform tables and their public addresses. -/
def verifyK (p : Params) (S : Nat) : Contract isa where
  pre s := vPre p S s ∧ StaticRoots S s
  post := (verifyContract p abi S).post
  pub s t := vPub p S s t ∧ RootSymbolsEq s t

theorem shared_pub {p : Params} {S : Nat} {s t : State}
    (h : (verifyContract p (abi.withConsts signRootConsts) S).pub s t) :
    vPub p S s t ∧ RootSymbolsEq s t := by
  sig_pub [verifyContract,verifySig,abi,argRegs,Abi.withConsts,Sign.signRootConsts_eq] at h
  obtain ⟨hsp,hf,hi,hb,h0,h1,h2,h3⟩ := h
  refine ⟨?_,hf,hi⟩
  unfold vPub
  sig_pub [verifyContract,verifySig,abi,argRegs]
  exact ⟨hsp,hb,h0,h1,h2,h3⟩

theorem verifyK_implies {p : Params} (hp : Ok3 p) :
    (verifyK p 16).Implies (verifyContract p (abi.withConsts signRootConsts) 16) where
  pre := fun _ h=>entry (by decide) h
  post := by
    sig_implies_post [verifyK,verifyContract,verifySig,abi,argRegs,Abi.withConsts]
  pub := fun _ _ _ _ h=>shared_pub h
  sat := ⟨verifySat p,verify_sat hp⟩

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedVerified.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem verify_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    Piece p S (fun σ s=>s=σ ∧ Sign.StaticRoots S s)
      (fun σ s=>abiPreserved σ s ∧ (verifyContract p abi S).post σ s)
      (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith keccak.callee P p) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.verifyWith
  exact (Piece.of_vpiece (OptimizedSamples.rooted_piece (pro_vpiece hF)
    (by change 0≤S;omega) hP.s64)).seq
    ((body_piece hP hF).seq (Piece.of_vpiece (epi_vpiece hF)))

/-- Exact optimized verification under the unchanged public algorithm,
with only the two immutable artifact tables supplied by the ABI. -/
theorem verify_verified {P : Prims} (hP : PrimsOk P 16) {p : Params}
    (hp : p=mlDsa44∨p=mlDsa65∨p=mlDsa87) :
    Verified target (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith keccak.callee P p)
      (verifyContract p (abi.withConsts Sign.signRootConsts) 16) := by
  apply Verified.of_correct (k:=verifyK p 16)
  · intro σ h
    exact (verify_piece hP (vfacts hp)).ok σ σ h.1 ⟨rfl,h.2⟩
  · intro s t ts tt u v hs ht pub es et
    exact ((verify_piece hP (vfacts hp)).tr _ _ _ _ _ _
      ⟨⟨s,t,hs.1,ht.1,pub.1,⟨rfl,hs.2⟩,⟨rfl,ht.2⟩⟩,pub.2⟩ es et).1
  · exact verifyK_implies hp

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedDepth.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Message

/-- The selected arithmetic kernels have no nested stack frame; only the
existing sponge calls need the 16-byte stack reservation. -/
theorem verify_dle (v : Proof.Sha3.AArch64.Permutation) {P : Prims}
    (hP : PrimsOk P 16) (p : Params) :
    DLe 1 (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee P p) := by
  obtain ⟨ha,hpad,hs⟩ := keccak_dle v
  have hh := DLe.of_fd hP.hintUnpack.fd
  have hu := DLe.of_fd hP.bitUnpack.fd
  have ht := DLe.of_fd hP.unpackT1.fd
  have hnorm := DLe.of_fd hP.normLt.fd
  have hsample := DLe.of_fd (OptimizedSamples.samples_depth hP p)
  have hn := DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.positiveNtt_callee 16).fd
  have hi := DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.Inverse.inverseSingle_callee 16).fd
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.MontDot.dot p.ℓ) := by
    unfold Impl.MlDsa.AArch64.Optimized.MontDot.dot
    dle_tac
  have hm : DLe 1 Impl.MlDsa.AArch64.Optimized.MontProduct.code := by
    unfold Impl.MlDsa.AArch64.Optimized.MontProduct.code
    dle_tac
  have hsub : DLe 1 (Impl.MlDsa.AArch64.Optimized.AddSub.code true) := by
    unfold Impl.MlDsa.AArch64.Optimized.AddSub.code
    dle_tac
  have hpack : DLe 1 Impl.MlDsa.AArch64.Optimized.UseHintPack.prog := by
    unfold Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
      Impl.MlDsa.AArch64.Round.zext Impl.MlDsa.AArch64.Round.onGamma
      Impl.MlDsa.AArch64.Optimized.UseHintPack.code
    dle_tac
  unfold Impl.MlDsa.AArch64.Verify.Optimized.verifyWith
    Impl.MlDsa.AArch64.Verify.Optimized.bodyWith
    Impl.MlDsa.AArch64.Verify.Optimized.computeWith
  repeat' (first
    | with_reducible assumption
    | (apply DLe.call; with_reducible assumption)
    | apply DLe.seq
    | apply DLe.ite
    | apply DLe.loop
    | (apply DLe.seqR; intro)
    | apply DLe.block)

/-- Every standard optimized raw verifier fits the existing stack budget,
for either verified Keccak permutation. -/
theorem verifyWith_dle (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    DLe 1 (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee (primsWith v.callee) p) :=
  verify_dle v (KeyGen.prims_okWith (keccak:=v)) p

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Message/OptimizedVerifyCorrect.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_movz)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)

theorem verifyMessage_wp (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hV : VerifyFn p c) (hp : p ∈ params) {s : State} (hpre : (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre s) :
    WP isa (verifyMessage v.callee n c p) s fun s' =>
      abiPreserved s s' ∧ (verifyMessageContract p (abi.withConsts signRootConsts) 16).post s s' := by
  have h := vPre_of hpre
  unfold verifyMessage top
  refine WP.seq (WP.mono_syms (lsr_ok s) fun s1 ⟨o1, hc1⟩ hy1 => ?_)
  by_cases h8 : (s.gpr .x4).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := vlay_ok hp h h8
    refine wp_ite_f hc1 (WP.seq (WP.mono_syms (enter_ok hL rfl (by decide) rfl (o1.get .x6) (by rw [o1.sp]; rfl)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .x4) (verifySaves_vals o1) (by decide))
      fun t hc hyt => ?_))
    refine WP.seq (WP.seq (WP.mono_syms (trHash_ok v hL rfl hc) fun t₁ ⟨hc₁, htr⟩ hytr => ?_))
    have hst : Region.Sub ⟨(vlay p s).ST, 200⟩ (vlay p s).XS := by
      have := Offset.sub_base (vlay p s).X (d := 0) (n := 200) (k := 1024) (by omega)
      simpa only [x0] using this
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    refine WP.seq (WP.mono_syms (muHash_ok v hL hc₁ (tr := .off oMU) (by decide) rfl (fun t' hc' => hc'.off oMU)
      ⟨R, by simp [hR], hw⟩ st_mu.symm mu_ks (k_mu hL)) fun t₂ ⟨hc₂, hμ⟩ hymu => ?_)
    have hroots : StaticRoots 16 t₂ := roots_ctx h (by simpa only [o1.mem] using hc₂)
      (hymu.trans (hytr.trans (hyt.trans hy1)))
    refine WP.mono (verifyCall_ok hV hp h h8 hc₂ hroots) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (leave_ok hL hf) fun s'' ⟨hcs, hsp, hvs, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), hsp,
      fun r hr => (hvs r hr).trans (o1.vcs r hr)⟩, ?_⟩
    sig_post [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.signRootConsts_eq, List.range, List.range.loop]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [verifyInternal, messageRep, pkTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₂.mem (s.gpr .x0) p.pkLen = bytesAt s.mem (s.gpr .x0) p.pkLen :=
      (hc₂.bytesAt_eq (p := (vlay p s).key) (n := p.pkLen) hL.xKey hL.kKey (by have := h.nPk; omega)).trans
        (by rw [hm₀]; rfl)
    have es : bytesAt t₂.mem (s.gpr .x5) p.sigLen = bytesAt s.mem (s.gpr .x5) p.sigLen :=
      (hc₂.bytesAt_eq (p := (vlay p s).sig) (n := p.sigLen) (h.sigScr.symm.sub_left (vlay_X p s).sub) h.stkSig
        (by have := h.nSig; omega)).trans (by rw [hm₀]; rfl)
    have hμ' := hμ
    rw [show (vlay p s).X + BitVec.ofNat 64 oMU = (vlay p s).MU from rfl, htr, hm₀] at hμ'
    rw [ek, es, hμ'] at hq
    rw [hx0]
    simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine wp_ite_t hc1 (wp_movz fun s2 o2 e2 => wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp],
      fun r hr => by rw [o2.vcs r hr, o1.vcs r hr]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.x0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h9 : r ∉ [Reg.x9] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.get r h0, o1.get r h9]
    · sig_post [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.signRootConsts_eq, List.range,
        List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), e2]
      rfl

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Message/OptimizedVerifyCallTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open Message.Optimized (rootRegions rootPairRegions rootsAt rootsAt_syms)
variable {p : Params}
/-- The layout is that of a run of `verify_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def VOk (p : Params) (L : Lay) (m : Mem) : Prop :=
  ∃ σ, VPre p σ ∧ (σ.gpr .x4).toNat < 256 ∧ vlay p σ = L ∧ σ.mem = m

theorem VOk.facts {L : Lay} {m : Mem} (h : VOk p L m) : VFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.sigScr.symm.sub_left (vlay_X p σ).sub, hσ.stkSig, hσ.nSig, by simp [vlay, hσ.rd],
    ⟨⟨σ.gpr .x6, mScrLen p⟩, by simp [vlay, hσ.wr], within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩,
    ⟨⟨σ.gpr .x6, mScrLen p⟩, by simp [vlay, hσ.wr], mu_withinV p σ⟩⟩

/-- Two runs of the call of the verification function on `μ`. -/
theorem verifyCall_tr (tab : Addr × Addr) {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m t => VOk p L m ∧ VMuOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab) (callA n c verifyArgs)
      fun _ _ => True := by
  refine Message.Optimized.call_tr (by decide) hV.ver.1 hV.ver.2.1
    (fun L => [⟨L.key, p.pkLen⟩, ⟨L.MU, 64⟩, ⟨L.sig, p.sigLen⟩]++rootPairRegions tab) (fun L => [⟨L.scr, sScr p⟩])
    (fun L g v m₀ t t1 hL hc hφ hm => ?_) (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g v m₀ t hL hc hφ => ?_)
  · obtain ⟨⟨σ,hσ,h8,rfl,_⟩,_,hr,htab⟩ := hφ
    have H := verifyK_pre hp hσ h8 hc hm.1 hm.2 hr
    have etab : rootRegions t1=rootPairRegions tab := by
      change rootPairRegions (rootsAt t1)=rootPairRegions tab
      rw [rootsAt_syms hm.2,htab]
    simpa only [etab,verifyRd,verifyWr,vlay] using H
  · obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁.1
    have F := φ₁.1.facts
    obtain ⟨x0, x1, x2, x3⟩ := verifyRegs_of c₁ f₁.1.1
    obtain ⟨y0, y1, y2, y3⟩ := verifyRegs_of c₂ f₂.1.1
    have ek : ∀ {g v m₀} {a a1 : State}, Ctx (vlay p σ) g v m₀ a → Moved verifyArgs a a1 →
        bytesAt a1.mem (σ.gpr .x0) p.pkLen = bytesAt m₀ (σ.gpr .x0) p.pkLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (vlay p σ).key) hL.xKey hL.kKey (by have := hL.nKey; simp only [vlay] at this ⊢; omega)
    have es : ∀ {g v m₀} {a a1 : State}, Ctx (vlay p σ) g v m₀ a → Moved verifyArgs a a1 →
        bytesAt a1.mem (σ.gpr .x5) p.sigLen = bytesAt m₀ (σ.gpr .x5) p.sigLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (vlay p σ).sig) F.xSig F.kSig (by have := F.nSig; omega)
    have eμ : ∀ {a a1 : State}, Moved verifyArgs a a1 →
        bytesAt a1.mem (vlay p σ).MU 64 = bytesAt a.mem (vlay p σ).MU 64 := fun f => by rw [f.2.mem]
    obtain ⟨ik, im, ic, is⟩ := verifyI_eq hi
    sig_pub [verifyContract, verifySig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.signRootConsts_eq, List.range, List.range.loop]
    simp only [x0, x1, x2, x3, y0, y1, y2, y3, and_true]
    refine ⟨by rw [f₁.1.2.sp, f₂.1.2.sp, c₁.sp, c₂.sp], ?_⟩
    have etab : rootsAt a1=rootsAt b1 := by
      rw [rootsAt_syms f₁.2,rootsAt_syms f₂.2,φ₁.2.2.2,φ₂.2.2.2]
    refine ⟨congrArg Prod.fst etab,congrArg Prod.snd etab,?_⟩
    rw [ek c₁ f₁.1,ek c₂ f₂.1,es c₁ f₁.1,es c₂ f₂.1,eμ f₁.1,eμ f₂.1,φ₁.2.1,φ₂.2.1]
    have ik' : bytesAt m₁ (σ.gpr .x0) p.pkLen = bytesAt m₂ (σ.gpr .x0) p.pkLen := ik
    have is' : bytesAt m₁ (σ.gpr .x5) p.sigLen = bytesAt m₂ (σ.gpr .x5) p.sigLen := is
    rw [ik, im, ic, ik', is']
  · have F := hφ.1.facts
    have hw : Covers [⟨L.scr,sScr p⟩] L.wr := by
      refine covers_of_within fun r hr=>?_
      simp only [List.mem_singleton] at hr
      subst r; exact F.inScr
    refine ⟨Covers.append_left ?_ hw.right,hw⟩
    apply Covers.append_left
    · refine covers_of_within fun r hr=>?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨_,List.mem_append_left _ (F.key ▸ hL.inKey),within_self _⟩
      · obtain ⟨R,hR,hw⟩ := F.inMu; exact ⟨R,by simp [hR],hw⟩
      · exact ⟨_,List.mem_append_left _ F.inSig,within_self _⟩
    · have ht := Covers.pair hφ.2.2.1.forward.readable hφ.2.2.1.inverse.readable
      change Covers (rootPairRegions (rootsAt t)) (t.rd++t.wr) at ht
      simpa only [hφ.2.2.2,hc.rd,hc.wr] using ht

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Message/OptimizedVerifyBodyTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open Message.Optimized (rootRegions rootPairRegions rootsAt rootsAt_syms)
variable {p : Params}

theorem hash_depth (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    16*(trHash v.callee p).aarch64Depth≤16 ∧
    16*(muHash v.callee (.off oMU)).aarch64Depth≤16 := by
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  have hd : DLe 1 (trHash v.callee p) := by
    unfold trHash kabs kpad ksqz callA
    dle_tac
  have hm : DLe 1 (muHash v.callee (.off oMU)) := by
    unfold muHash kabs kpad ksqz callA
    dle_tac
  have := hd.le; have := hm.le; omega
/-- The body, between the entry and the exit: its runs end with the same
`x28` and stack pointer. -/
theorem verifyBody_tr (tab : Addr × Addr) (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hV : VerifyFn p c)
    (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m t => VOk p L m ∧ StaticRoots 16 t ∧ rootsAt t=tab)
      (.seq (trHash v.callee p) (.seq (muHash v.callee (.off oMU)) (callA n c verifyArgs)))
      fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp := by
  have th := trHash_tr v (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ StaticRoots 16 t ∧ rootsAt t=tab) (pkLen_ge hp).2
    (fun _ _ _ h => h.1.facts.key)
  have th' := two_wp (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ StaticRoots 16 t ∧ rootsAt t=tab) (Ψ := fun L m t => VOk p L m ∧ TrOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab) th
    fun L g vv m₀ t hL hc ⟨hφ,hr,htab⟩ =>
      WP.mono_syms (hr.phase (hash_depth v p).1 (by decide) (trHash_ok v hL hφ.facts.key hc))
        fun t' ⟨⟨hc',htr⟩,hr'⟩ hsy=>
          ⟨hc',hφ,by unfold TrOk; rw [htr,hφ.facts.key],hr',by rw [rootsAt_syms hsy,htab]⟩
  have side : ∀ L : Lay, L.Ok → (∃ R ∈ L.rd ++ L.wr, Within ⟨L.MU, 64⟩ R) ∧
      Region.Disjoint ⟨L.MU, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.MU, 64⟩ := fun L hL => by
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    exact ⟨⟨R, by simp [hR], hw⟩, st_mu.symm, mu_ks, k_mu hL⟩
  have mh := muHash_tr v (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ TrOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab) (tr := .off oMU)
    (by decide) rfl (fun L => L.MU) (fun L g vv m t hc => hc.off oMU) side
  have mh' := two_wp (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ TrOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab)
    (Ψ := fun L m t => VOk p L m ∧ VMuOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab) mh fun L g vv m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d⟩ := side L hL
      refine WP.mono_syms (hφ.2.2.1.phase (hash_depth v p).2 (by decide)
        (muHash_ok v hL hc (tr := .off oMU) (by decide) rfl (fun t' hc' => hc'.off oMU) a b c d))
        fun t' ⟨⟨hc',hμ⟩,hr'⟩ hsy => ⟨hc',hφ.1,?_,hr',by rw [rootsAt_syms hsy,hφ.2.2.2]⟩
      unfold VMuOk
      rw [hμ]
      have h2 := hφ.2.1
      unfold TrOk at h2
      rw [show L.X + BitVec.ofNat 64 oMU = L.MU from rfl, h2]
  refine RelCT.postDep (F := fun x x' => x'.gpr .x28 = x.gpr .x28 ∧ x'.sp = x.sp)
    (th'.seq (mh'.seq (verifyCall_tr tab hV hp))) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : Lay} {g vv m₀} {t : State}, L.Ok → Ctx L g vv m₀ t → (VOk p L m₀ ∧ StaticRoots 16 t ∧ rootsAt t=tab) →
        WP isa (.seq (trHash v.callee p) (.seq (muHash v.callee (.off oMU)) (callA n c verifyArgs))) t
          fun t' => t'.gpr .x28 = t.gpr .x28 ∧ t'.sp = t.sp := fun hL hc ⟨hφ,hr,_⟩ => by
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d⟩ := side _ hL
      refine WP.seq (WP.mono (hr.phase (hash_depth v p).1 (by decide) (trHash_ok v hL rfl hc)) fun t₁ ⟨⟨hc₁,_⟩,hr₁⟩ => ?_)
      refine WP.seq (WP.mono (hr₁.phase (hash_depth v p).2 (by decide) (muHash_ok v hL hc₁ (tr := .off oMU) (by decide) rfl
        (fun t' hc' => hc'.off oMU) a b c d)) fun t₂ ⟨⟨hc₂,_⟩,hr₂⟩ => ?_)
      exact WP.mono (verifyCall_ok hV hp hσ h8 hc₂ hr₂) fun s' ⟨hf, _⟩ =>
        ⟨hf.x28.trans hc.x28.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.x28, c₂.x28], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩


end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Message/OptimizedVerifyTopTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open Message.Optimized (rootRegions rootsAt rootsAt_syms)
variable {p : Params}

structure VPub (p : Params) (s t : State) extends Message.VPub p s t where
  roots : rootsAt s=rootsAt t

theorem vPub_of {s t : State}
    (h : (verifyMessageContract p (abi.withConsts signRootConsts) 16).pub s t) : VPub p s t := by
  sig_pub [verifyMessageContract,verifyMessageSig,abi,argRegs,Abi.withConsts,Sign.signRootConsts_eq,
    List.range,List.range.loop] at h
  obtain ⟨sp,hf,hi,leak,x0,x1,x2,x3,x4,x5,x6⟩ := h
  exact ⟨⟨sp,leak,x0,x1,x2,x3,x4,x5,x6⟩,Prod.ext hf hi⟩

theorem vlay_eq {s t : State} (hs : VPre p s) (ht : VPre p t) (h : VPub p s t) : vlay p s=vlay p t := by
  have hf := congrArg Prod.fst h.roots
  have hi := congrArg Prod.snd h.roots
  have er : s.rd=t.rd := by
    rw [hs.rd,ht.rd]
    simp only [rKey,rMsg,rCtx,rootRegions,h.x0,h.x1,h.x2,h.x3,h.x4,h.x5] at hf hi ⊢
    rw [hf,hi]
  have ew : s.wr=t.wr := by rw [hs.wr,ht.wr,h.x6]
  simp only [vlay,h.sp,h.x0,h.x1,h.x2,h.x3,h.x4,h.x5,h.x6,er,ew]

abbrev VP2 (p : Params) (x y : State) : Prop :=
  (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre x ∧
  (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre y ∧
  (verifyMessageContract p (abi.withConsts signRootConsts) 16).pub x y

theorem verifyMessage_ct (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hV : VerifyFn p c)
    (hp : p ∈ params) :
    ConstantTime isa (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre (verifyMessageContract p (abi.withConsts signRootConsts) 16).pub
      (verifyMessage v.callee n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre s₁ ∧
      (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre s₂ ∧ (verifyMessageContract p (abi.withConsts signRootConsts) 16).pub s₁ s₂) =
      Ghost (VP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessage top
  -- `x9 ← ctx_len >> 8`.
  have hlsr := ghost_step (P := VP2 p) (A := fun x a => a = x) (B := fun x a => ALsr x a ∧ a.syms=x.syms) (c := .block [.lsr .x .x9 .x4 8])
    (AArch64.taintRel [] (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨(vPub_of hxy.2.2).sp, by simp⟩) lsr_taint)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩), WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩)⟩
  refine RelCT.seq hlsr (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.1.2, f₂.1.2, (vPub_of hxy.2.2).x4]) ?_ ?_)
  · -- `ctx_len ≥ 256`: return 2.
    exact AArch64.taintRel [] (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ =>
      ⟨by rw [f₁.1.1.sp, f₂.1.1.sp]; exact (vPub_of hxy.2.2).sp, by simp⟩) movz2_taint
  · -- The entry.
    let A : State → State → Prop := fun x a => (ALsr x a ∧ a.syms=x.syms) ∧ isa.eval (.nonzero .x .x9) a = some false
    let B : State → State → Prop := fun x t => (x.gpr .x4).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (vlay p x) a.gpr a.v a.mem t ∧ t.syms=x.syms
    have hent := ghost_step (P := VP2 p) (A := A) (B := B) (c := .block (enter .x6 p verifySaves))
      (AArch64.taintRel [.x6] (fun a b ⟨x, y, hxy, f₁, f₂⟩ => ⟨by rw [f₁.1.1.1.sp, f₂.1.1.1.sp]; exact (vPub_of hxy.2.2).sp,
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [f₁.1.1.1.get .x6, f₂.1.1.1.get .x6]; exact (vPub_of hxy.2.2).x6⟩) (enterV_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre x' → A x' a' →
            WP isa (.block (enter .x6 p verifySaves)) a' (B x') := fun x' a' hx ⟨⟨⟨o, e⟩, hy⟩, ef⟩ => by
          have h8 : (x'.gpr .x4).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have hL := vlay_ok hp (vPre_of hx) h8
          exact WP.mono_syms (enter_ok hL rfl (by decide) rfl (o.get .x6) (by rw [o.sp]; rfl) (by rw [o.rd]; rfl)
            (by rw [o.wr]; rfl) (o.get .x4) (verifySaves_vals o) (by decide)) fun t hc hyt => ⟨h8, a', o.mem, hc, hyt.trans hy⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.1.2, ← (vPub_of hxy.2.2).x4, ← f₁.1.2]; exact hc⟩⟩) fun _ _ h => h) (RelCT.seq (RelCT.mono (RelCT.exists_ fun tab => verifyBody_tr tab v hV hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca, sya⟩,
      ⟨h8y, b', mb, cb, syb⟩⟩ => ?_) fun _ _ h => h) (AArch64.taintRel [.x28] (fun a b h => ⟨h.2, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1⟩) leave_taint))
    have hx := vPre_of hxy.1
    have hy := vPre_of hxy.2.1
    have hpub := vPub_of hxy.2.2
    have e := vlay_eq hx hy hpub
    refine ⟨rootsAt x, vlay p x, a'.gpr, b'.gpr, a'.v, b'.v, a'.mem, b'.mem, vlay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨⟨x, hx, h8x, rfl, ma.symm⟩, roots_ctx hx (by simpa only [ma] using ca) sya, rootsAt_syms sya⟩,
      ⟨⟨y, hy, h8y, e.symm, mb.symm⟩, roots_ctx hy (by simpa only [mb] using cb) syb,
        (rootsAt_syms syb).trans hpub.roots.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.x0, ← hpub.x1, ← hpub.x2, ← hpub.x3, ← hpub.x4, ← hpub.x5] at lk
    unfold verifyI
    rw [ma, mb]
    exact lk


end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Message/OptimizedVerifyVerified.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts)

/-- The ordinary message verifier retains its existing result and public-input
contract while supplying both immutable transform tables to the verified callee. -/
theorem verifyMessage_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p∈params) :
    Verified target (verifyMessage v.callee n c p)
      (verifyMessageContract p (abi.withConsts signRootConsts) 16) :=
  ⟨fun _ h=>let ⟨t,s',he,ha,hq⟩ := verifyMessage_wp v hV hp h; ⟨t,s',he,ha,hq⟩,
    verifyMessage_ct v hV hp,⟨verifySat p,verify_sat (by simpa only [Sign.Ok3,params,List.mem_cons,List.not_mem_nil,or_false] using hp)⟩⟩

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/RootedCachedVerifyVerified.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts)

/-- Cached-key message verification with both immutable transform tables,
original public leakage, and the unchanged cached-digest semantics. -/
theorem verifyMessage_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} {n : String} {c : Prog isa}
    (hV : Message.OptimizedVerify.VerifyFn p c) (hp : p ∈ params) :
    Verified AArch64.target (verifyMessageCached v.callee n c p)
      (verifyMessageCachedContract p (abi.withConsts signRootConsts) 16) := by
  refine ⟨fun _ h=>let ⟨tr,t,he,ha,hq⟩:=verifyMessageCached_wp v hV hp h;⟨tr,t,he,ha,hq⟩,
    verifyMessage_ct v hV hp,verifySat p,verify_sat ?_⟩
  simpa only [Sign.Ok3,params,List.mem_cons,List.not_mem_nil,or_false] using hp

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Verify.Optimized

/-- The feature-selected raw verifier shared by all public wrappers. -/
def selectedCode (v : Proof.Sha3.AArch64.Permutation) (p : Params) : Prog isa :=
  if v.callee.pairedSha3 then
    Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p
  else Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p

def selectedConsts (v : Proof.Sha3.AArch64.Permutation) : List (String × List (BitVec 64)) :=
  if v.callee.pairedSha3 then Sign.signRootConsts else []

def selectedAbi (v : Proof.Sha3.AArch64.Permutation) : Abi isa :=
  abi.withConsts (selectedConsts v)

theorem selected_verify_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p) :
    Verified target (selectedCode v p) (verifyContract p (selectedAbi v) 16) := by
  unfold selectedCode selectedAbi selectedConsts
  split
  · exact Optimized.verify_verified (keccak:=v) (KeyGen.prims_okWith (keccak:=v)) hp
  · exact Verify.verify_verified (keccak:=v) (KeyGen.prims_okWith (keccak:=v)) p hp (Verify.verify_sat p hp)

theorem optimizedVerifyFn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p) :
    Message.OptimizedVerify.VerifyFn p
      (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) :=
  ⟨Optimized.verify_verified (keccak:=v) (KeyGen.prims_okWith (keccak:=v)) hp,verifyWith_dle v p⟩

theorem selected_message_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    (n : String) :
    Verified target (Impl.MlDsa.AArch64.Message.verifyMessage v.callee n (selectedCode v p) p)
      (verifyMessageContract p (selectedAbi v) 16) := by
  have hm : p∈Message.params := by simpa only [Sign.Ok3,Message.params,List.mem_cons,List.not_mem_nil,or_false] using hp
  unfold selectedCode selectedAbi selectedConsts
  split
  · exact Message.OptimizedVerify.verifyMessage_verified v (optimizedVerifyFn v hp) hm
  · exact Message.verifyMessage_verified v (Message.verifyFn v hm) hm

theorem selected_cached_message_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    (n : String) :
    Verified target (Impl.MlDsa.AArch64.Optimized.verifyMessageCached v.callee n (selectedCode v p) p)
      (verifyMessageCachedContract p (selectedAbi v) 16) := by
  have hm : p∈Message.params := by simpa only [Sign.Ok3,Message.params,List.mem_cons,List.not_mem_nil,or_false] using hp
  unfold selectedCode selectedAbi selectedConsts
  split
  · exact VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify.verifyMessage_verified v (optimizedVerifyFn v hp) hm
  · exact VG.Proof.MlDsa.AArch64.Optimized.CachedVerify.verifyMessage_verified v (Message.verifyFn v hm) hm

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected
