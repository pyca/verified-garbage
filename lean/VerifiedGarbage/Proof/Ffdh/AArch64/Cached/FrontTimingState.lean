module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateFront
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportPrefixTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InverseUnique
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ScalarRangeTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicRangeTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CombTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.KeyStatus
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateBody

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
/-! Public and secret inputs of the context-import and entropy-sampling front end. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/BodyTimingState.lean`, which only this module imported.
section

/-! Attempt timing fixes only the reviewed public status, with independent secret draws. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure BodyPublic where
 scalar : ScalarPublic
 yp : Addr
 status : Nat
 bitsPositive : 0<scalar.p.N
 bitsBound : scalar.p.N≤8192
 width : scalar.p.N≤8*scalar.p.k
 table : scalar.p.table=scalar.p.ctx+BitVec.ofNat 64 (24+16*scalar.p.w)
 valid : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf scalar.p.k scalar.dom)=true
 outsideX : ∀ i<scalar.p.k,scalar.p.Z≤ofs scalar.p.B (scalar.p.src+BitVec.ofNat 64 i)

structure BodyState (q : BodyPublic) (bs : List Byte) (s : State) : Prop where
 scalar : ScalarState q.scalar bs s
 bound : Spec.Rsa.os2ip bs<2^q.scalar.p.N
 status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.scalar.p.k q.scalar.dom) (Spec.Rsa.os2ip bs)=q.status
 y : word s.mem q.scalar.p.B (8*sY)=q.yp
 write : ∀ i<q.scalar.p.k,InRegions s.wr (q.scalar.p.src+BitVec.ofNat 64 i) 1

def BodyReady (q : BodyPublic) (s : State) : Prop := ∃ bs,BodyState q bs s

def bodyOutput (q : BodyPublic) : OutputPublic :=
 ⟨q.scalar.p,q.yp,q.scalar.words,q.scalar.positive,q.scalar.size,q.outsideX⟩

def bodyComb (q : BodyPublic) : CombPublic :=
 ⟨⟨q.scalar.p,q.bitsPositive,q.bitsBound,q.scalar.size,q.width⟩,q.table⟩

theorem bodyReady_output {q : BodyPublic} {s : State} (h : BodyReady q s) : OutputReady (bodyOutput q) s := by
 obtain ⟨bs,h⟩:=h
 exact ⟨h.scalar.initial.good,h.scalar.initial.controls.source,h.y,h.scalar.length ▸ h.scalar.initial.controls.length,h.write⟩

def BodyRangeDone (q : BodyPublic) (s : State) : Prop :=
 BodyReady q s ∧ s.gpr .x9=(if q.status=2 then 0#64 else 1#64)

theorem bodyRangeDone_ok {q : BodyPublic} {s : State} (h : BodyReady q s) :
 WP isa Generate.scalarRange s (BodyRangeDone q) := by
 obtain ⟨bs,h⟩:=h
 have init :=h.scalar.initial
 refine WP.mono (scalarRange_ok init.good q.scalar.p.room q.scalar.words q.scalar.positive q.scalar.size q.scalar.shape q.scalar.domLength
  h.scalar.source (source_src init.reads.source init.reads.scalarOutside) h.scalar.length init.controls.source h.scalar.domain
  (h.scalar.length ▸ init.controls.length) h.scalar.domainLength (init.modulus.trans q.scalar.modulus)
  (by rw [←q.scalar.modulus];exact q.scalar.odd)) ?_
 rintro t ⟨good,_,flag,frame,rest⟩
 have state : BodyState q bs t :=
  ⟨h.scalar.after good frame rest,h.bound,h.status,(scalarFrame_header frame (by decide) (by decide)).trans h.y,
   fun i hi =>by rw [rest.wr];exact h.write i hi⟩
 refine ⟨⟨bs,state⟩,?_⟩
 have rejected := keyStatus_scalar_rejected q.valid (Spec.Rsa.os2ip bs)
 rw [h.status] at rejected
 by_cases scalar : 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf q.scalar.p.k q.scalar.dom)
 · rw [ite_eq_left scalar] at flag
   rw [ite_eq_right (fun eq =>rejected.mp eq scalar)]
   exact flag
 · rw [ite_eq_right scalar] at flag
   rw [ite_eq_left (rejected.mpr scalar)]
   exact flag

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GenerateBodyTiming.lean`, which only this module imported.
section

/-! Complete attempt-body timing is governed by public geometry and the reviewed returned status. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)

def TailReady (q : BodyPublic) (s : State) : Prop :=
 ModState q.scalar.p s ∧ OutputReady (bodyOutput q) s

def bodyRangePublic (q : BodyPublic) : RangePublic :=
 ⟨scalarWs q.scalar,by change 0<q.scalar.p.w;have :=q.scalar.p.positive;omega,q.scalar.p.width⟩

theorem bodyComb_output (M : Mont) {q : BodyPublic} {s : State} (h : BodyReady q s) :
 WP isa (Comb.code M.mm) s (TailReady q) := by
 obtain ⟨bs,h⟩ :=h
 have length :=h.scalar.length
 refine WP.mono (comb_correct M h.scalar.initial q.bitsPositive q.bitsBound
  (length ▸ q.scalar.size) (length ▸ q.width) h.bound q.table) ?_
 rintro t ⟨state,_,controls,_,stable,rest⟩
 exact ⟨state,state.good,controls.source,
  (stable sY (by decide) (by decide) (by decide) (by decide)).trans h.y,
  length ▸ controls.length,fun i hi =>by rw [rest.wr];exact h.write i hi⟩

theorem bodyRange_finish {q : BodyPublic} {s : State} (h : TailReady q s) :
 WP isa Generate.publicRange s (FinishReady (bodyOutput q)) := by
 obtain ⟨state,good,x,y,len,write⟩ :=h
 refine WP.mono (publicRange_ok state q.scalar.odd) ?_
 rintro t ⟨stateT,_,flag,header,frame,rest⟩
 refine ⟨⟨stateT.good,(publicRangeFrame_header frame (by decide) (by decide)).trans x,
  (publicRangeFrame_header frame (by decide) (by decide)).trans y,
  (publicRangeFrame_header frame (by decide) (by decide)).trans len,
  fun i hi =>by rw [rest.wr];exact write i hi⟩,?_,?_⟩
 · exact decide (1<wv s.mem q.scalar.p.B (slot q.scalar.p.w 6) q.scalar.p.w ∧
    wv s.mem q.scalar.p.B (slot q.scalar.p.w 6) q.scalar.p.w<q.scalar.p.P-1)
 · change word t.mem q.scalar.p.B (8*sTmp)=_
   rw [header,flag]
   exact (bit_decide _).symm

theorem acceptedBody_ct (M : Mont) : RelCT isa (Two BodyReady)
 (.seq (Comb.code M.mm) (.seq Generate.publicRange Generate.finish)) (fun _ _ =>True) := by
 refine RelCT.seq (two_post (Ψ:=TailReady)
  (two_map bodyComb (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨bs,h.scalar.initial,h.bound⟩) (comb_ct M))
  (fun _ _ h =>bodyComb_output M h)) ?_
 exact RelCT.seq (two_post (Ψ:=fun q s =>FinishReady (bodyOutput q) s)
  (two_map bodyRangePublic (fun q s h =>⟨q.scalar.p.mi,h.1.good,q.scalar.p.room⟩) publicRange_ct)
  (fun _ _ h =>bodyRange_finish h)) (two_map bodyOutput (fun _ _ h =>h) finish_ct)

theorem generateBody_ct (M : Mont) : RelCT isa (Two BodyReady) (generateBody M.mm) (fun _ _ =>True) := by
 unfold generateBody
 refine RelCT.seq (two_post (Ψ:=BodyRangeDone)
  (two_map BodyPublic.scalar (fun _ _ h =>by obtain ⟨bs,h⟩:=h;exact ⟨bs,h.scalar⟩) scalarRange_ct)
  (fun _ _ h =>bodyRangeDone_ok h)) ?_
 refine RelCT.ite ?_ ?_ ?_
 · rintro s t ⟨q,hs,ht,_⟩
   rw [eval_zero,eval_zero,hs.2,ht.2]
 · exact (two_map bodyOutput (fun _ _ h =>bodyReady_output h) fail_ct).mono
    (fun _ _ h =>by rcases h.1 with ⟨q,hs,ht,sp⟩;exact ⟨q,hs.1,ht.1,sp⟩) (fun _ _ h =>h)
 · exact (acceptedBody_ct M).mono
    (fun _ _ h =>by rcases h.1 with ⟨q,hs,ht,sp⟩;exact ⟨q,hs.1,ht.1,sp⟩) (fun _ _ h =>h)

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure FrontPublic where
 body : BodyPublic
 rp : Addr
 count : Nat
 checked : Spec.Ffdh.domainValid body.scalar.p.k body.scalar.dom=true
 generator : body.scalar.p.G=(Spec.Ffdh.domainOf body.scalar.p.k body.scalar.dom).g
 policy : body.scalar.p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf body.scalar.p.k body.scalar.dom)
 separateRand : ∀ i<body.scalar.p.k,∀ j<body.scalar.p.k,rp+BitVec.ofNat 64 i≠body.scalar.p.src+BitVec.ofNat 64 j
 separateDomain : ∀ i<body.scalar.dom.length,body.scalar.p.k≤ofs body.scalar.p.src (body.scalar.dp+BitVec.ofNat 64 i)
 separateContext : ∀ i<8*count,body.scalar.p.k≤ofs body.scalar.p.src (body.scalar.p.ctx+BitVec.ofNat 64 i)

structure FrontState (q : FrontPublic) (rb : List Byte) (s : State) : Prop where
 scratch : Scr s q.body.scalar.p.B q.body.scalar.p.Z
 base : s.gpr .x0=q.body.scalar.p.B
 view : ContextView q.body.scalar.p.B q.body.scalar.p.Z q.body.scalar.p.ctx q.count q.body.scalar.p.k q.body.scalar.dom s
 domainSource : Src s q.body.scalar.p.B q.body.scalar.p.Z q.body.scalar.dp q.body.scalar.dom
 randomSource : Src s q.body.scalar.p.B q.body.scalar.p.Z q.rp rb
 rbLength : rb.length=q.body.scalar.p.k
 controls : Controls q.body.scalar.p.B q.body.scalar.p.src q.body.scalar.p.ctx q.body.scalar.p.k q.body.scalar.p.N s
 domain : word s.mem q.body.scalar.p.B (8*sDom)=q.body.scalar.dp
 domainLength : word s.mem q.body.scalar.p.B (8*sDL)=BitVec.ofNat 64 q.body.scalar.dl
 y : word s.mem q.body.scalar.p.B (8*sY)=q.body.yp
 random : word s.mem q.body.scalar.p.B (8*sRand)=q.rp
 bytes : word s.mem q.body.scalar.p.B (8*sBytes)=BitVec.ofNat 64 ((q.body.scalar.p.N+7)/8)
 write : ∀ i<q.body.scalar.p.k,InRegions s.wr (q.body.scalar.p.src+BitVec.ofNat 64 i) 1
 status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom)
  (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) rb)=q.body.status

def FrontReady (q : FrontPublic) (s : State) : Prop := ∃ rb,FrontState q rb s

def frontImport (q : FrontPublic) : ImportPublic :=
 ⟨scalarWs q.body.scalar,q.body.scalar.p.k,q.body.scalar.p.ctx,q.body.scalar.p.room,
  q.body.scalar.words,q.body.scalar.positive,q.body.scalar.size⟩

def frontSample (q : FrontPublic) : SamplePublic :=
 ⟨scalarWs q.body.scalar,q.body.scalar.p.room,q.body.scalar.p.k,q.body.scalar.p.N,
  q.body.scalar.p.src,q.rp,q.body.bitsPositive,q.body.bitsBound⟩

def frontBody (q : FrontPublic) (mi : BitVec 64) : BodyPublic :=
 {q.body with scalar:={q.body.scalar with p:={q.body.scalar.p with mi:=mi}}}

theorem frontReady_import {q : FrontPublic} {s : State} (h : FrontReady q s) : ImportReady (frontImport q) s := by
 obtain ⟨rb,h⟩:=h
 exact ⟨h.scratch,h.base,h.controls.length,h.controls.context,
  fun i hi =>by
   change i<2*q.body.scalar.p.w at hi
   change InRegions (s.rd++s.wr) (off q.body.scalar.p.ctx (24+8*i)) 8
   have count :=context_words_count h.view.canonical
   have readable :=h.view.readable (3+i) (by change 3+i<q.count;rw [count];change _<3+34*((q.body.scalar.p.k+7)/8);rw [←q.body.scalar.words];omega)
   simpa only [off,Nat.mul_add,Nat.reduceMul] using readable,
  fun i hi =>by
   change i<16*q.body.scalar.p.w at hi
   change q.body.scalar.p.Z≤ofs q.body.scalar.p.B (off q.body.scalar.p.ctx 24+BitVec.ofNat 64 i)
   have count :=context_words_count h.view.canonical
   have outside :=h.view.outside (24+i) (by rw [count];change _<8*(3+34*((q.body.scalar.p.k+7)/8));rw [←q.body.scalar.words];omega)
   simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using outside⟩

theorem frontImport_sample {q : FrontPublic} {s : State} (h : FrontReady q s) :
 WP isa importPrefix s (SampleReady (frontSample q)) := by
 obtain ⟨rb,h⟩:=h
 have ready :=frontReady_import (q:=q) ⟨rb,h⟩
 have domSize : q.body.scalar.p.k≤q.body.scalar.dom.length := by have :=q.body.scalar.shape;have :=q.body.scalar.domLength;omega
 have values :=context_prefix domSize (VG.Proof.Ffdh.domainValid_mod q.checked) h.view.canonical
 have wEq : q.body.scalar.p.w=Spec.Rsa.modulusWords q.body.scalar.p.k :=q.body.scalar.words
 rw [←wEq,←q.body.scalar.modulus] at values
 refine WP.mono (importPrefix_ok h.scratch h.base q.body.scalar.p.room q.body.scalar.words q.body.scalar.positive q.body.scalar.size
  h.controls.length h.controls.context ready.readable ready.outside values.1 values.2 q.body.scalar.odd) ?_
 rintro t ⟨mi,good,_,_,_,frame,_⟩
 have same (i : Nat) (lo : 16≤i) (hi : i<32) :=importFrame_header frame lo hi
 exact ⟨⟨mi,good,q.body.scalar.p.room⟩,(same sBits (by decide) (by decide)).trans h.controls.bits,
  (same sBytes (by decide) (by decide)).trans h.bytes,(same sLen (by decide) (by decide)).trans h.controls.length,
  (same sX (by decide) (by decide)).trans h.controls.source,(same sRand (by decide) (by decide)).trans h.random⟩

end VG.Proof.Ffdh.AArch64.Cached
