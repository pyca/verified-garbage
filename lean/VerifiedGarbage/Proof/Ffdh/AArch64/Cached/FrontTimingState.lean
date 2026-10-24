module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateFront
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateBodyTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportPrefixTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InverseUnique
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Public and secret inputs of the context-import and entropy-sampling front end. -/
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
