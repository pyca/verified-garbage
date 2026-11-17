module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedSecrets
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.MlDsa.BoundedFourContract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call

/-! ### `MlDsa.AArch64.Optimized.BoundedFourCallTiming`, which this module and modules that import it used -/

section

/-! ## From `BoundedFourCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)

theorem sampler_callee (S : Nat) (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) :
    CalleeOk S (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (rejBoundedFourContract abi η) :=
by
  refine CalleeOk.of_ct (sampler_verified sha3 hη).1 (sampler_verified sha3 hη).2.1 (by rcases hη with rfl|rfl <;> cases sha3 <;> lit_decide) (fun _ _ h => h) ?_
  have hd : (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η).aarch64Depth=0 := by
    rcases hη with rfl|rfl <;> cases sha3 <;> decide
  rw [hd]
  exact Nat.zero_le _

abbrev samplerArgs (seed out work : Ptr) : List (Reg × Arg) :=
 [(.x0,.ptr seed),(.x1,.ptr out),(.x2,.ptr work)]

structure CallReady (seed out work : Ptr) (s : State) : Prop where
 seedFit : (pa s seed).toNat+264≤2^64
 outFit : (pa s out).toNat+4096≤2^64
 workFit : (pa s work).toNat+8192≤2^64
 seedOut : (⟨pa s seed,264⟩ : Region).Disjoint ⟨pa s out,4096⟩
 seedWork : (⟨pa s seed,264⟩ : Region).Disjoint ⟨pa s work,8192⟩
 outWork : (⟨pa s out,4096⟩ : Region).Disjoint ⟨pa s work,8192⟩
 readable : Covers [⟨pa s seed,264⟩,⟨pa s out,4096⟩,⟨pa s work,8192⟩] (s.rd++s.wr)
 writable : Covers [⟨pa s out,4096⟩,⟨pa s work,8192⟩] s.wr

theorem samplerAt_pre {η : Nat} (hη : η=2∨η=4) {s s1 : State} {seed out work : Ptr}
    (h : CallReady seed out work s) (h1 : Args (samplerArgs seed out work) s s1) :
    (rejBoundedFourContract abi η).pre
      (s1.callEntry.withRegions [⟨pa s seed,264⟩] [⟨pa s out,4096⟩,⟨pa s work,8192⟩]) := by
  sig_pre [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Arg.val]
  exact ⟨trivial,trivial,h.seedOut,h.seedWork,h.outWork,h.seedFit,h.outFit,h.workFit,hη⟩

theorem samplerArgs_ok {seed out work : Ptr}
    (hs : (Arg.ptr seed).Ok) (ho : (Arg.ptr out).Ok) (hw : (Arg.ptr work).Ok) :
    ∀x∈samplerArgs seed out work,x.2.Ok ∧ x.1∈argRegs := by
  simp only [samplerArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl
  · exact ⟨hs,by simp⟩
  · exact ⟨ho,by simp⟩
  · exact ⟨hw,by simp⟩

theorem samplerAt_ok {S : Nat} (hS : S<2^64) (sha3 : Bool) {η : Nat} (hη : η=2∨η=4)
    {nm : String} {s : State} {seed out work : Ptr}
    (hs : (Arg.ptr seed).Ok) (ho : (Arg.ptr out).Ok) (hw : (Arg.ptr work).Ok)
    (h : CallReady seed out work s) :
    WP isa (callAt nm (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (samplerArgs seed out work)) s fun t=>
      Post S s t [⟨pa s out,4096⟩,⟨pa s work,8192⟩] ∧
      (∀i<4,Reduced t.mem (pa s out+BitVec.ofNat 64 (1024*i))) ∧
      (∀i<4,BoundedOutput η t.mem (pa s out+BitVec.ofNat 64 (1024*i))) ∧
      Outcome (fun b=>(rejBoundedFour η b.rejBounded s.mem (pa s seed)).map (List.map toRq))
        ((t.gpr .x0).setWidth 32)
        ((List.range 4).map fun i=>polyAt t.mem (pa s out+BitVec.ofNat 64 (1024*i))) := by
  refine WP.mono (callAtSyms_ok hS (sampler_callee S sha3 hη) (samplerArgs_ok hs ho hw) (by simp)
    (fun s1 h1 _=>samplerAt_pre hη h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩=>?_
  sig_post [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.mem h1] at hq
  exact ⟨hP,hq⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)

theorem samplerAt_tr {S : Nat} (sha3 : Bool) {η : Nat} (hη : η=2∨η=4)
    {nm : String} {seed out work : Ptr}
    (hs : (Arg.ptr seed).Ok) (ho : (Arg.ptr out).Ok) (hw : (Arg.ptr work).Ok)
    {Q : State→State→Prop}
    (hQ : ∀s t,Q s t→CallReady seed out work s ∧ CallReady seed out work t ∧
      pa s seed=pa t seed ∧ pa s out=pa t out ∧ pa s work=pa t work ∧ s.sp=t.sp ∧
      rejBoundedFourLeak η s.mem (pa s seed)=rejBoundedFourLeak η t.mem (pa t seed)) :
    RelCT isa Q (callAt nm (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (samplerArgs seed out work)) (fun _ _=>True) := by
  refine callAtSyms_tr (sampler_callee S sha3 hη) (samplerArgs_ok hs ho hw) (by simp)
    fun s t s1 t1 hp h1 h2 _ _=>?_
  obtain ⟨rs,rt,es,eo,ew,esp,el⟩:=hQ s t hp
  refine ⟨[⟨pa s seed,264⟩],[⟨pa s out,4096⟩,⟨pa s work,8192⟩],
    samplerAt_pre hη rs h1,?_,?_,rs.readable,rs.writable,?_,?_⟩
  · rw [es,eo,ew]; exact samplerAt_pre hη rt h2
  · sig_pub [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.sp h1,Args.sp h2,Args.mem h1,Args.mem h2]
    exact ⟨esp,el,es,eo,ew⟩
  · rw [es,eo,ew]; exact rt.readable
  · rw [eo,ew]; exact rt.writable

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.Optimized

theorem boundedReady {S : Nat} {p : Params} (hF : PFacts p) {s : State}
    (L : Lay S kgR (kgW p) s) {r : Nat} (hr : r+4≤p.ℓ+p.k+1) :
    BoundedFour.CallReady (sc 1408) (sP p r) (sc (oR4 p)) s := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hs : inB (kgR++kgW p) (sc 1408) 264=true := by layd
  have ho : inB (kgR++kgW p) (sP p r) 4096=true := by layd
  have hw : inB (kgR++kgW p) (sc (oR4 p)) 8192=true := by layd
  have hwo : inB (kgW p) (sP p r) 4096=true := by layd
  have hww : inB (kgW p) (sc (oR4 p)) 8192=true := by layd
  have hso : sepB kgR (kgW p) (sc 1408) 264 (sP p r) 4096=true := by layd
  have hsw : sepB kgR (kgW p) (sc 1408) 264 (sc (oR4 p)) 8192=true := by layd
  have how : sepB kgR (kgW p) (sP p r) 4096 (sc (oR4 p)) 8192=true := by layd
  exact ⟨L.nwp hs,L.nwp ho,L.nwp hw,L.disj hso,L.disj hsw,L.disj how,
    Covers.cons (L.cR hs) (Covers.cons (L.cR ho) (L.cR hw)),Covers.cons (L.cW hwo) (L.cW hww)⟩

theorem boundedAt_layout {S : Nat} {p : Params} (hF : PFacts p) {s : State}
    (L : Lay S kgR (kgW p) s) {r : Nat} (hr : r+4≤p.ℓ+p.k+1)
    (c : Impl.Sha3.AArch64.Callee) :
    WP isa (callAt (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.boundedFourSymbol c p.η)
      (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler c.pairedSha3 true p.η)
      (BoundedFour.samplerArgs (sc 1408) (sP p r) (sc (oR4 p)))) s fun t=>
      PPostB S s t [(sP p r,4096),(sc (oR4 p),8192)] ∧ t.gpr .x24=s.gpr .x24 ∧
      (∀i<4,Reduced t.mem (pa s (sP p r)+BitVec.ofNat 64 (1024*i))) ∧
      (∀i<4,BoundedOutput p.η t.mem (pa s (sP p r)+BitVec.ofNat 64 (1024*i))) ∧
      Outcome (fun b=>(rejBoundedFour p.η b.rejBounded s.mem (pa s (sc 1408))).map (List.map toRq))
        ((t.gpr .x0).setWidth 32)
        ((List.range 4).map fun i=>polyAt t.mem (pa s (sP p r)+BitVec.ofNat 64 (1024*i))) := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hs : inB (kgR++kgW p) (sc 1408) 264=true := by layd
  have ho : inB (kgR++kgW p) (sP p r) 4096=true := by layd
  have hw : inB (kgR++kgW p) (sc (oR4 p)) 8192=true := by layd
  have hη : p.η=2∨p.η=4 := by rcases hF.eta with h|h; exact Or.inl h.1; exact Or.inr h.1
  refine WP.mono (BoundedFour.samplerAt_ok L.s64 c.pairedSha3 hη
    (ptr_ok (L.ptrBs hs)) (ptr_ok (L.ptrBs ho)) (ptr_ok (L.ptrBs hw)) (boundedReady hF L hr))
    fun t ⟨hp,hred,hsmall,hout⟩=>?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hred,hsmall,hout⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
