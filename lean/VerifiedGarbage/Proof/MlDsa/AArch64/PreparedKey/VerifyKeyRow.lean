module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.ReadCache
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Verify
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
public import VerifiedGarbage.Proof.MlDsa.Arith.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCall
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Optimized
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedState
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackTiming
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.UseHintPack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackSpec
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotVerified
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontDot
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductVerified
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls

/-! ### `MlDsa.AArch64.Verify.OptimizedRowStart`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized

abbrev W (p : Params) (σ : State) (A' : Nat→Nat→Poly) (r : Nat) (s : State) : Prop :=
  PolyIs s.mem (pa s (wP p)) ((rDot p σ A' r).map (·*montgomeryRInv))

theorem unpack_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A' : Nat→Nat→Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s) :
    WP isa (unpackT1At P (.x25,32+320*r) (tmP p)) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧ W p σ A' r t ∧ PolyIs t.mem (pa t (tmP p)) (rU p σ r) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr;have hpk:=hF.pk
  have hc : rwChk (vR p) (vW p) (.x25,32+320*r) 320 (tmP p) 1024=true := by unfold rwChk;vlay
  refine WP.mono_syms (t1At_ok hP.s64 hP.unpackT1 L hc) fun t ⟨hb,h24,hv⟩ hy=>?_
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;vlay) h24,
    L.keepPoly hb (by vlayd) hw,?_⟩
  rw [hs.vc.pkSlice (by rw [hF.pk];omega_using [hr])] at hv
  rw [hb.pa (show Reg.x28∈keptRegs by decide)]
  exact hv

theorem nttT_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s)
    (ht : PolyIs s.mem (pa s (tmP p)) (rU p σ r)) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.forward (tmP p)) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧ W p σ A' r t ∧
      PosPolyIs t.mem (pa t (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have rd : inB (vR p++vW p) (tmP p) 1024=true := by vlayd
  have wr : inB (vW p) (tmP p) 1024=true := by vlayd
  refine WP.mono_syms (Sign.positiveNttAt_layout L rd wr
    ⟨hs.roots.nttTableAt (L.inW wr),hs.roots.forward.readable⟩ ht.1)
    fun t ⟨hb,h24,hv⟩ hy=>?_
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wr) h24,
    L.keepPoly hb (by vlayd) hw,?_⟩
  rw [hb.pa (show Reg.x28∈keptRegs by decide)]
  rw [ht.2] at hv
  exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedRowProduct`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.MontProductCallTiming`, which this module and modules that import it used -/

section

/-! ## From `MontProductCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontProduct (code)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem callee (S : Nat) : CalleeOk S code (montProductContract abi) :=
  CalleeOk.of_ct verified.1 verified.2.1 (by lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev args (out a b : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b)]

structure Ready (out a b : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024≤2^64
  bFit : (pa s b).toNat+1024≤2^64
  outA : (polyRegion (pa s out)).Disjoint (polyRegion (pa s a))
  outB : (polyRegion (pa s out)).Disjoint (polyRegion (pa s b))
  positiveA : PositiveReduced s.mem (pa s a)
  positiveB : PositiveReduced s.mem (pa s b)
  readable : Covers [polyRegion (pa s a),polyRegion (pa s b),polyRegion (pa s out)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s out)] s.wr

theorem at_pre {s s1 : State} {out a b : Ptr}
    (h : Ready out a b s) (h1 : Args (args out a b) s s1) :
    (montProductContract abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s a),polyRegion (pa s b)] [polyRegion (pa s out)]) := by
  sig_pre [montProductContract,montProductSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,Arg.val]
  exact ⟨trivial,trivial,h.outA,h.outB,h.outFit,h.aFit,h.bFit,h.positiveA,h.positiveB⟩

theorem args_ok {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) :
    ∀x∈args out a b,x.2.Ok ∧ x.1∈argRegs := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩

theorem at_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    (h : Ready out a b s) :
    WP isa (callAt nm code (args out a b)) s fun t =>
      Post S s t [polyRegion (pa s out)] ∧
      PolyIs t.mem (pa s out) (montgomeryMultiplyNTT (polyAt s.mem (pa s a)) (polyAt s.mem (pa s b))) := by
  refine WP.mono (callAtSyms_ok hS (callee S) (args_ok ho ha hb) (by simp)
    (fun s1 h1 _=>at_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [montProductContract,montProductSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end

/-! ## From `MontProductCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontProduct (code)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem at_tr {S : Nat} {nm : String} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → Ready out a b x ∧ Ready out a b z ∧
      pa x out=pa z out ∧ pa x a=pa z a ∧ pa x b=pa z b ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm code (args out a b)) fun _ _=>True := by
  refine callAtSyms_tr (callee S) (args_ok ho ha hb) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,eo,ea,eb,esp⟩ := hQ x z hp
  refine ⟨[polyRegion (pa x a),polyRegion (pa x b)],[polyRegion (pa x out)],
    at_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb]; exact at_pre rz h2
  · sig_pub [montProductContract,montProductSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,eo,ea,eb⟩
  · rw [eo,ea,eb]; exact rz.readable
  · rw [eo]; exact rz.writable
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Arith.Montgomery

theorem product_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s)
    (ht : PosPolyIs s.mem (pa s (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.product p) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧ W p σ A' r t ∧
      PolyIs t.mem (pa t (tm2P p))
        (montgomeryMultiplyNTT (ntt c0) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)) := by
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
  refine WP.mono_syms (MontProduct.at_ok L.s64 (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) ready) fun t ⟨hp',hv⟩ hy=>?_
  have hb : PPostB S s t [(tm2P p,1024)] := hp'.b
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wo)
    (hp'.cs .x24 (by decide) (by decide)),L.keepPoly hb (by vlayd) hw,?_⟩
  rw [hb.pa (L.ptrBs ro)]
  rwa [hc.value,ht.value] at hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedDot`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.MontDotCallTiming`, which this module and modules that import it used -/

section

/-! ## From `MontDotCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontDot (dot)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem callee (S : Nat) {count : Nat} (hc : count=4∨count=5∨count=7) : CalleeOk S (dot count) (montDotContract abi count) :=
  CalleeOk.of_ct (verified hc).1 (verified hc).2.1 (by rcases hc with rfl|rfl|rfl <;> lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev args (out a b : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b)]

def family (p : Addr) (n : Nat) : Region := ⟨p,1024*n⟩

structure Ready (count : Nat) (out a b : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024*count≤2^64
  bFit : (pa s b).toNat+1024*count≤2^64
  outA : (polyRegion (pa s out)).Disjoint (family (pa s a) count)
  outB : (polyRegion (pa s out)).Disjoint (family (pa s b) count)
  positiveA : ∀j<count,PositiveReduced s.mem (pa s a+BitVec.ofNat 64 (1024*j))
  positiveB : ∀j<count,PositiveReduced s.mem (pa s b+BitVec.ofNat 64 (1024*j))
  readable : Covers [family (pa s a) count,family (pa s b) count,polyRegion (pa s out)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s out)] s.wr

theorem at_pre {s s1 : State} {count : Nat} {out a b : Ptr}
    (h : Ready count out a b s) (h1 : Args (args out a b) s s1) :
    (montDotContract abi count).pre
      (s1.callEntry.withRegions [family (pa s a) count,family (pa s b) count] [polyRegion (pa s out)]) := by
  sig_pre [montProductContract,montDotSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,Arg.val]
  have he : 256*count*4=1024*count := by omega_using []
  rw [he]
  exact ⟨rfl,trivial,h.outA,h.outB,h.outFit,h.aFit,h.bFit,h.positiveA,h.positiveB⟩

theorem args_ok {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) :
    ∀x∈args out a b,x.2.Ok ∧ x.1∈argRegs := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩

theorem at_ok {S : Nat} (hS : S<2^64) {count : Nat} (hc : count=4∨count=5∨count=7) {nm : String} {s : State} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    (h : Ready count out a b s) :
    WP isa (callAt nm (dot count) (args out a b)) s fun t =>
      Post S s t [polyRegion (pa s out)] ∧
      PolyIs t.mem (pa s out) ((dotNTT (fun j=>polyAt s.mem (pa s a+BitVec.ofNat 64 (1024*j)))
        (fun j=>polyAt s.mem (pa s b+BitVec.ofNat 64 (1024*j))) count).map (·*montgomeryRInv)) := by
  refine WP.mono (callAtSyms_ok hS (callee S hc) (args_ok ho ha hb) (by simp)
    (fun s1 h1 _=>at_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [montProductContract,montDotSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontDot (dot)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem at_tr {S : Nat} {count : Nat} (hc : count=4∨count=5∨count=7) {nm : String} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → Ready count out a b x ∧ Ready count out a b z ∧
      pa x out=pa z out ∧ pa x a=pa z a ∧ pa x b=pa z b ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm (dot count) (args out a b)) fun _ _=>True := by
  refine callAtSyms_tr (callee S hc) (args_ok ho ha hb) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,eo,ea,eb,esp⟩ := hQ x z hp
  refine ⟨[family (pa x a) count,family (pa x b) count],[polyRegion (pa x out)],
    at_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb]; exact at_pre rz h2
  · sig_pub [montDotContract,montDotSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,eo,ea,eb⟩
  · rw [eo,ea,eb]; exact rz.readable
  · rw [eo]; exact rz.writable
end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

end

end

@[expose] public section

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

theorem dot_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.dot p r) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧
      PolyIs t.mem (pa t (wP p)) ((dotAcc p (vSig p σ) A' r p.ℓ).map (·*montgomeryRInv)) := by
  have L := hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hrow : p.ℓ*r+p.ℓ≤p.k*p.ℓ := by
    have hm:=Nat.mul_le_mul_left p.ℓ (show r+1≤p.k by omega_using [hr])
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
    have he : p.k*p.ℓ+(1+p.k+j)=(p.k*p.ℓ+(1+p.k))+j := by omega_using []
    rw [he,poly_addr] at hv
    simpa only [zP,vP,Nat.add_zero] using hv
  have ready : MontDot.Ready p.ℓ (wP p) (aP (p.ℓ*r)) (zP p 0) s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.disj (by vlayd),L.disj (by vlayd),
      fun j hj=>(PosPolyIs.of_canonical (hA j hj)).bound,fun j hj=>(hB j hj).bound,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  refine WP.mono_syms (MontDot.at_ok L.s64 hn (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) ready) fun t ⟨hP,hv⟩ hy=>?_
  have hb : PPostB S s t [(wP p,1024)] := hP.b
  have hw : w1Len p * r ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) (Nat.le_of_lt hr); rw [Nat.mul_comm (w1Len p) p.k] at this
    have := hF.w1; omega_arith
  have hc : SCChk p r [(wP p, 1024)] :=
    SCChk.x28 hF (Nat.le_of_lt hr) (.inr (by simp only [SV, oP]; omega_using [])) (.inr (by simp only [oP]; omega_using []))
      (.inr (by simp only [oP]; omega_using [hw])) (.inr (by simp only [oP]; omega_using [])) (by rw [hsc]; simp only [oP]; omega_using [])
  refine ⟨hs.keep hF hp hb hc hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wo)
    (hP.cs .x24 (by decide) (by decide)),?_⟩
  rw [hb.pa (L.ptrBs ro)]
  have he : dotNTT (fun j=>polyAt s.mem (pa s (aP (p.ℓ*r))+BitVec.ofNat 64 (1024*j)))
      (fun j=>polyAt s.mem (pa s (zP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ=
      dotAcc p (vSig p σ) A' r p.ℓ := by
    unfold dotNTT
    rw [←foldl_dot]
    apply congrArg (List.foldl add zero)
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    dsimp only
    rw [(hA j hj).2,(hB j hj).value]
  simpa only [he] using hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedHintPack`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.UseHintPackCallTiming`, which this module and modules that import it used -/

section

/-! ### `MlDsa.UseHintPackContract`, which only this module used -/

section

/-!
# ML-DSA: the contract of `UseHint`, packed

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- The fixed-gamma API retains the measured four-register ABI. -/
def useHintPackSig (g : Nat) : Sig where
  params := [("out", .array true .u8 (32*bitlen ((q-1)/(2*g)-1))),
    ("hints", .array false .u32 256), ("w", .array false .u32 256), ("gamma2", .int .u32 true)]

/-- Exact composition of FIPS 204 UseHint and SimpleBitPack. Every nonzero
hint word is interpreted as true, just as in the separate UseHint helper. -/
def useHintPackContract (g : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (useHintPackSig g).contract A
    (pre := fun _out _h w gamma m => gamma.toNat=g ∧ g∈gamma2s ∧ Reduced m w)
    (post := fun out h w _gamma m m' _ =>
      Spec.Sha3.bytesAt m' out (32*bitlen ((q-1)/(2*g)-1)) =
        simpleBitPack (Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
          ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m w)) ((q-1)/(2*g)-1))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa

end

end

/-! ### `MlDsa.AArch64.Optimized.UseHintPackVerified`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open HighPack (packWidth)

def packSat (g : Nat) : State where
  gpr r := match r with | .x0=>0x1000 | .x1=>0x2000 | .x2=>0x3000 | .x3=>BitVec.ofNat 64 g | _=>0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000,1024⟩,⟨0x3000,1024⟩]
  wr := [⟨0x1000,32*packWidth g⟩]

/-- Fused UseHint and encoding against the architecture-independent shared specification. -/
theorem pack_verified {g : Nat} (hg : IsG g) :
    Verified AArch64.target Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
      (useHintPackContract g AArch64.abi) := by
  refine Verified.of_correct (pack_correct hg) pack_ct ?_
  refine {pre:=?_,post:=?_,pub:=?_,sat:=?_}
  · rcases hg with rfl|rfl <;>
      (intro s h
       sig_pre [useHintPackContract,useHintPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs] at h
       sig_split h
       sig_reduce [packK,packWidth,arg32]
       exact ⟨by assumption,by assumption,by apply Region.Disjoint.symm; assumption,by apply Region.Disjoint.symm; assumption,by assumption,by assumption⟩)
  · intro s t hp hpost
    have hr : Reduced s.mem (s.gpr .x2) := by
      rcases hg with rfl|rfl <;>
        (sig_pre [useHintPackContract,useHintPackSig,AArch64.abi,AArch64.argRegs] at hp
         sig_split hp
         exact hp)
    have hs := packed_spec hg (h:=s.gpr .x1) hr
    rcases hg with rfl|rfl <;>
      (sig_post [useHintPackContract,useHintPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs]
       exact hpost.trans hs)
  · rcases hg with rfl|rfl <;>
      sig_implies_pub [useHintPackContract,useHintPackSig,packK,AArch64.abi,AArch64.argRegs]
  · refine ⟨packSat g,?_⟩
    rcases hg with rfl|rfl <;>
      sig_pre [useHintPackContract,useHintPackSig,AArch64.abi,AArch64.argRegs] <;> sig_and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | exact fun i _=>by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero];decide
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

end


/-! ## From `UseHintPackCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.UseHintPack (prog)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem callee (S : Nat) {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) : CalleeOk S prog (useHintPackContract g abi) :=
  CalleeOk.of_ct (pack_verified hg).1 (pack_verified hg).2.1 (by lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev args (out a b : Ptr) (g : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b),(.x3,.imm g)]

abbrev packLen (g : Nat) := 32*bitlen ((q-1)/(2*g)-1)

structure CallReady (out a b : Ptr) (g : Nat) (s : State) : Prop where
  outFit : (pa s out).toNat+packLen g≤2^64
  aFit : (pa s a).toNat+1024≤2^64
  bFit : (pa s b).toNat+1024≤2^64
  outA : (⟨pa s out,packLen g⟩ : Region).Disjoint (polyRegion (pa s a))
  outB : (⟨pa s out,packLen g⟩ : Region).Disjoint (polyRegion (pa s b))
  gamma : VG.Proof.MlDsa.AArch64.Round.IsG g
  canonical : Reduced s.mem (pa s b)
  readable : Covers [polyRegion (pa s a),polyRegion (pa s b),⟨pa s out,packLen g⟩] (s.rd++s.wr)
  writable : Covers [⟨pa s out,packLen g⟩] s.wr

theorem at_pre {s s1 : State} {out a b : Ptr} {g : Nat}
    (h : CallReady out a b g s) (h1 : Args (args out a b g) s s1) :
    (useHintPackContract g abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s a),polyRegion (pa s b)] [⟨pa s out,packLen g⟩]) := by
  sig_pre [useHintPackContract,useHintPackSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.mem h1,Arg.val]
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by
    rcases h.gamma with rfl|rfl <;> decide
  rw [hg]
  exact ⟨trivial,trivial,h.outA,h.outB,h.outFit,h.aFit,h.bFit,rfl,
    VG.Proof.MlDsa.AArch64.Round.mem_of_isG h.gamma,h.canonical⟩

theorem args_ok {out a b : Ptr} {g : Nat}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) :
    ∀x∈args out a b g,x.2.Ok ∧ x.1∈argRegs := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩
  · exact ⟨trivial,by simp⟩

theorem at_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {out a b : Ptr} {g : Nat}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    (h : CallReady out a b g s) :
    WP isa (callAt nm prog (args out a b g)) s fun t =>
      VG.Proof.MlDsa.AArch64.Post S s t [⟨pa s out,packLen g⟩] ∧
      Spec.Sha3.bytesAt t.mem (pa s out) (packLen g)=
        simpleBitPack (Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
          ((hintAt s.mem (pa s a) 1).headD (Vector.replicate n false)) (polyAt s.mem (pa s b)))
          ((q-1)/(2*g)-1) := by
  refine WP.mono (callAtSyms_ok hS (callee S h.gamma) (args_ok ho ha hb) (by simp)
    (fun s1 h1 _=>at_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [useHintPackContract,useHintPackSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.UseHintPack (prog)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem at_tr {S : Nat} {nm : String} {out a b : Ptr} {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → CallReady out a b g x ∧ CallReady out a b g z ∧
      pa x out=pa z out ∧ pa x a=pa z a ∧ pa x b=pa z b ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm prog (args out a b g)) fun _ _=>True := by
  refine callAtSyms_tr (callee S hg) (args_ok ho ha hb) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,eo,ea,eb,esp⟩ := hQ x z hp
  refine ⟨[polyRegion (pa x a),polyRegion (pa x b)],[⟨pa x out,packLen g⟩],
    at_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb]; exact at_pre rz h2
  · sig_pub [useHintPackContract,useHintPackSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.r3 h1,Args.r3 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,eo,ea,eb,rfl⟩
  · rw [eo,ea,eb]; exact rz.readable
  · rw [eo]; exact rz.writable
end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Verify (wRow w1Row)

theorem hintPack_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (wRow p (vPk p σ) (vSig p σ) A' (ntt c0) r)) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.hintPack p r) s (SC p S σ h A' c0 q p.ℓ true (r+1)) := by
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
  refine WP.mono_syms (UseHintPack.at_ok L.s64 (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) ready) fun t ⟨hp',hv⟩ hy=>?_
  have hb : PPostB S s t [(rowP p r,w1Len p)] := hp'.b
  have ht := hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wo)
    (hp'.cs .x24 (by decide) (by decide))
  refine ⟨ht.vc,ht.roots,ht.hh,ht.hint,ht.nok,ht.gd,ht.a,ht.z,ht.c,fun j hj=>?_,ht.x24⟩
  rcases (by omega_using [hj] : j<r∨j=r) with hj'|rfl
  · exact ht.rows j hj'
  · rw [hb.pa (L.ptrBs ro)]
    rw [hintRow_pa p s j,Proof.MlDsa.Verify.hintAt_row hs.hint hr,hw.2] at hv
    exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedRowEnd`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseSingleCall`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

/-- Internal call contract for the same verified kernel. Its execution never
accesses the unused scratch argument of the separately emitted public helper. -/
theorem inverseSingle_callee (S : Nat) : CalleeOk S staticCode inverseK :=
  CalleeOk.of_ct inverse_correct inverse_ct (by lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev inverseSingleArgs (f : Ptr) : List (Reg × Arg) := [(.x0,.ptr f)]

structure InverseSingleReady (f : Ptr) (s : State) : Prop where
  held : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED")
  apart : (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (pa s f))
  reduced : Reduced s.mem (pa s f)
  readable : Covers [tableRegion (s.syms "VG_MLDSA_INV_FOLDED"),outputRegion (pa s f)] (s.rd++s.wr)
  writable : Covers [outputRegion (pa s f)] s.wr

theorem inverseSingle_pre {s s1 : State} {f : Ptr}
    (h : InverseSingleReady f s) (h1 : Args (inverseSingleArgs f) s s1)
    (hy : s1.syms=s.syms) :
    inverseK.pre (s1.callEntry.withRegions [tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]
      [outputRegion (pa s f)]) := by
  change tableRegion (s1.syms "VG_MLDSA_INV_FOLDED") ∈
      [tableRegion (s.syms "VG_MLDSA_INV_FOLDED"),outputRegion (pa s f)] ∧
    outputRegion (s1.callEntry.gpr .x0) ∈ [outputRegion (pa s f)] ∧
    (tableRegion (s1.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s1.callEntry.gpr .x0)) ∧
    InverseTable.Artifact s1.mem (s1.syms "VG_MLDSA_INV_FOLDED") ∧
    Reduced s1.mem (s1.callEntry.gpr .x0)
  rw [show s1.callEntry.gpr .x0=s1.gpr .x0 from rfl,Args.r0 h1,Args.mem h1,hy]
  exact ⟨by simp,by exact List.mem_singleton.mpr rfl,h.apart,h.held,h.reduced⟩

theorem inverseSingleArgs_ok {f : Ptr} (hf : (Arg.ptr f).Ok) :
    ∀x∈inverseSingleArgs f,x.2.Ok ∧ x.1∈argRegs := by
  intro x hx
  have he : x=(.x0,.ptr f) := by simpa only [inverseSingleArgs,List.mem_singleton] using hx
  subst x
  exact ⟨hf,by simp⟩

theorem inverseSingleAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {f : Ptr}
    (hf : (Arg.ptr f).Ok) (h : InverseSingleReady f s) :
    WP isa (callAt nm staticCode (inverseSingleArgs f)) s fun t =>
      Post S s t [outputRegion (pa s f)] ∧
      PolyIs t.mem (pa s f) (montgomeryNttInv (polyAt s.mem (pa s f))) := by
  refine WP.mono (callAtSyms_ok hS (inverseSingle_callee S) (inverseSingleArgs_ok hf) (by simp)
    (fun s1 h1 hy=>inverseSingle_pre h h1 hy) h.readable h.writable)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  change PolyIs t.mem (s1.callEntry.gpr .x0)
    (montgomeryNttInv (polyAt s1.mem (s1.callEntry.gpr .x0))) at hq
  rw [show s1.callEntry.gpr .x0=s1.gpr .x0 from rfl,Args.r0 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Arith.Montgomery

abbrev Diff (p : Params) (σ : State) (A' : Nat→Nat→Poly) (c0 : Poly) (r : Nat) : Poly :=
  sub (rDot p σ A' r) (multiplyNTT (ntt c0) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r))

theorem subtract_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s)
    (ht : PolyIs s.mem (pa s (tm2P p))
      (montgomeryMultiplyNTT (ntt c0) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r))) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.subtract p) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧
      PolyIs t.mem (pa t (wP p)) (scale montgomeryRInv (Diff p σ A' c0 r)) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : accChk (vR p) (vW p) (wP p) (tm2P p)=true := by unfold accChk;vlay
  have C : CalleeOk S (Impl.MlDsa.AArch64.Optimized.AddSub.code true) (subContract abi S) :=
    CalleeOk.of_verified L.s64 AddSub.sub_verified (Nat.zero_le _) (by change 0≤S;omega_using []) (by lit_decide)
  refine WP.mono_syms (accAt_ok L.s64 C L hc hw.1 ht.1) fun t ⟨hb,h24,hv⟩ hy=>?_
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;vlay) h24,?_⟩
  rw [hb.pa (show Reg.x28∈keptRegs by decide)]
  rw [hw.2,ht.2] at hv
  rw [Diff,scale_sub]
  exact hv

theorem inverse_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (scale montgomeryRInv (Diff p σ A' c0 r))) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.inverse (wP p)) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧
      PolyIs t.mem (pa t (wP p)) (Proof.MlDsa.Verify.wRow p (vPk p σ) (vSig p σ) A' (ntt c0) r) := by
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
  refine WP.mono_syms (Inverse.inverseSingleAt_ok L.s64 (ptr_ok (L.ptrBs rd)) ready)
    fun t ⟨hp',hv⟩ hy=>?_
  have hb : PPostB S s t [(wP p,1024)] := hp'.b
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wr)
    (hp'.cs .x24 (by decide) (by decide)),?_⟩
  rw [hb.pa (L.ptrBs rd)]
  rw [hw.2,inv_cancel] at hv
  exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

-- separate module: keeps cached-row contracts independent of the private verification composition that consumes them.

@[expose] public section

/-! ## VerifyCopy -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized

abbrev PublicCache (p : Params) (S : Nat) (σ s : State) : Prop :=
  ReadCache p.k S (fun r => VG.Proof.MlDsa.Verify.t1Hat (vPk p σ) r) s

theorem copy_public_optimized {p : Params} (hF : VFacts p) {S : Nat} {σ s : State}
    (hp : vPre p S σ) {h : List (Vector Bool n)} {A : Nat → Nat → Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r < p.k)
    (hs : Verify.Optimized.SC p S σ h A c0 q p.ℓ true r s)
    (hw : Verify.Optimized.W p σ A r s) (cache : PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy (tmP p) (.x21, 1024 * r) 1024) s fun t =>
      Verify.Optimized.SC p S σ h A c0 q p.ℓ true r t ∧
      Verify.Optimized.W p σ A r t ∧ PublicCache p S σ t ∧
      PosPolyIs t.mem (pa t (tmP p)) (VG.Proof.MlDsa.Verify.t1Hat (vPk p σ) r) := by
  have L := hs.vc.lay hF hp
  have hk := hF.k
  have hl := hF.l
  have hkl := hF.kl
  have hsc := hF.scr
  have hwrite : inB (vW p) (tmP p) 1024 = true := by vlayd
  refine WP.mono_syms (cache.copy_poly (show Reg.x28 ∈ keptRegs by decide)
    (L.inW hwrite) hr) fun t ⟨ht, h24, hc, hpoly⟩ hy => ?_
  refine ⟨hs.keep hF hp ht (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hw' => by obtain rfl := List.mem_singleton.mp hw'; exact hwrite) h24,
    L.keepPoly ht (by vlayd) hw, hc, PosPolyIs.of_canonical hpoly⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## VerifyKeyRow -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized

theorem keyRow_optimized
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A : Nat → Nat → Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r < p.k)
    (hs : Verify.Optimized.SC p S σ h A c0 q p.ℓ true r s)
    (hw : Verify.Optimized.W p σ A r s)
    (cache : s.gpr .x22 ≠ 0 → PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow P p r) s fun t =>
      Verify.Optimized.SC p S σ h A c0 q p.ℓ true r t ∧
      Verify.Optimized.W p σ A r t ∧
      PosPolyIs t.mem (pa t (tmP p)) (VG.Proof.MlDsa.Verify.t1Hat (vPk p σ) r) := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow
  refine WP.ite (M := isa) (s.gpr .x22 != 0) rfl (fun hn => ?_) (fun _ => ?_)
  · exact WP.mono (copy_public_optimized hF hp hr hs hw (cache (bne_iff_ne.mp hn)))
      fun _ ht => ⟨ht.1, ht.2.1, ht.2.2.2⟩
  · refine WP.seq (WP.mono (Verify.Optimized.unpack_ok hP hF hp hr hs hw)
      fun t ⟨ht, hw', hv⟩ => ?_)
    exact Verify.Optimized.nttT_ok hF hp hr ht hw' hv

theorem row_optimized
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A : Nat → Nat → Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r < p.k)
    (hdot : 16 * (Impl.MlDsa.AArch64.Verify.Optimized.dot p r).aarch64Depth ≤ S)
    (hrow : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r).aarch64Depth ≤ S)
    (hs : Verify.Optimized.SC p S σ h A c0 q p.ℓ true r s)
    (cache : s.gpr .x22 ≠ 0 → PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r) s fun t =>
      Verify.Optimized.SC p S σ h A c0 q p.ℓ true (r + 1) t ∧
      (t.gpr .x22 ≠ 0 → PublicCache p S σ t) := by
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r) s
      (Verify.Optimized.SC p S σ h A c0 q p.ℓ true (r + 1)) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.row
    refine WP.seq (WP.mono (WP.optionalCache (Verify.Optimized.dot_ok hF hp hr hs)
      cache hdot hP.s64
      (fun t ht => (ht.1.vc.top.cs .x21 (by decide)).trans (hs.vc.top.cs .x21 (by decide)).symm)
      (fun t ht => (ht.1.vc.top.cs .x22 (by decide)).trans (hs.vc.top.cs .x22 (by decide)).symm))
      fun t ⟨⟨ht, hw⟩, hc⟩ => ?_)
    refine WP.seq (WP.mono (keyRow_optimized hP hF hp hr ht hw hc)
      fun t ⟨ht, hw, hv⟩ => ?_)
    refine WP.seq (WP.mono (Verify.Optimized.product_ok hF hp hr ht hw hv)
      fun t ⟨ht, hw, hv⟩ => ?_)
    refine WP.seq (WP.mono (Verify.Optimized.subtract_ok hF hp hr ht hw hv)
      fun t ⟨ht, hw⟩ => ?_)
    refine WP.seq (WP.mono (Verify.Optimized.inverse_ok hF hp hr ht hw)
      fun t ⟨ht, hw⟩ => ?_)
    exact Verify.Optimized.hintPack_ok hF hp hr ht hw
  exact WP.optionalCache main cache hrow hP.s64
    (fun t ht => (ht.vc.top.cs .x21 (by decide)).trans (hs.vc.top.cs .x21 (by decide)).symm)
    (fun t ht => (ht.vc.top.cs .x22 (by decide)).trans (hs.vc.top.cs .x22 (by decide)).symm)

/-- The verification core, with the static root tables of its transforms. -/
def verifyCoreK (p : Params) : Contract isa where
  pre s := vPre p 16 s ∧ Sign.StaticRoots 16 s ∧
    (s.gpr .x22 ≠ 0 → PublicCache p 16 s s)
  post := (verifyContract p abi 16).post
  pub x y := vPub p 16 x y ∧
    (x.syms "VG_MLDSA_NTT_EXPANDED" = y.syms "VG_MLDSA_NTT_EXPANDED" ∧
      x.syms "VG_MLDSA_INV_FOLDED" = y.syms "VG_MLDSA_INV_FOLDED") ∧ SameIn [.x21, .x22] x y

end VG.Proof.MlDsa.AArch64.PreparedKey
