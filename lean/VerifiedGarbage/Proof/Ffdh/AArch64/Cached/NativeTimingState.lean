module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateEntry
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.FrontTimingState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratePrepared

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
/-! The cached attempt's public calling convention and immutable input geometry. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GenerateFrontTiming.lean`, which only this module imported.
section

/-! Relate independent entropy draws through context import, sampling, and the complete attempt. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- The inverse is reconstructed; no prior scratch value is assumed. -/
def FrontDone (q : FrontPublic) (s : State) : Prop := ∃ mi,BodyReady (frontBody q mi) s

theorem generateFront_ct : RelCT isa (Two FrontReady) (.seq importPrefix Generate.sample) (fun _ _ =>True) :=
 RelCT.seq (two_post (Ψ:=fun q s =>SampleReady (frontSample q) s)
  (two_map frontImport (fun _ _ h =>frontReady_import h) importPrefix_ct)
  (fun _ _ h =>frontImport_sample h)) (two_map frontSample (fun _ _ h =>h) sample_ct)

theorem front_done_ok {q : FrontPublic} {s : State} (h : FrontReady q s) :
 WP isa (.seq importPrefix Generate.sample) s (FrontDone q) := by
 obtain ⟨rb,h⟩:=h
 refine WP.mono (generateFront_ok h.scratch h.base q.body.scalar.words q.body.scalar.positive q.body.scalar.size q.body.scalar.shape
  q.body.scalar.domLength q.checked q.body.scalar.modulus q.generator q.policy q.body.table h.view h.domainSource h.randomSource h.rbLength
  h.controls h.domain h.domainLength h.y h.random h.bytes q.body.bitsPositive q.body.bitsBound q.body.width
  h.write q.body.outsideX q.separateRand q.separateDomain q.separateContext) ?_
 rintro t ⟨mi,initial,value,domainSource,domain,domainLength,y,rest⟩
 let bs:=Spec.Rsa.bytesAt t.mem q.body.scalar.p.src q.body.scalar.p.k
 refine ⟨mi,bs,⟨initial,initial.reads.length,domainSource,domain,domainLength⟩,?_,?_,y,?_⟩
 · change Spec.Rsa.os2ip bs<2^q.body.scalar.p.N
   rw [value]
   exact Nat.mod_lt _ (Nat.two_pow_pos _)
 · have scalar : Spec.Rsa.os2ip bs=Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) rb := by
    unfold Spec.Ffdh.vettedScalarOfOctets
    rw [←q.policy]
    exact value
   change Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) (Spec.Rsa.os2ip bs)=q.body.status
   rw [scalar];exact h.status
 · intro i hi;rw [rest.wr];exact h.write i hi

theorem front_done_two {s t : State} (h : Two FrontDone s t) :
 Two BodyReady s t := by
 obtain ⟨q,⟨a,bs,hs⟩,⟨b,bt,ht⟩,sp⟩:=h
 have same : a=b := imported_inverse_unique (p:=q.body.scalar.p)
  hs.scalar.initial.toFieldInitial ht.scalar.initial.toFieldInitial q.body.scalar.odd
 subst b
 exact ⟨frontBody q a,⟨bs,hs⟩,⟨bt,ht⟩,sp⟩

theorem generatePrepared_ct (M : Mont) :
 RelCT isa (Two FrontReady) (generatePrepared M.mm) (fun _ _ =>True) := by
 unfold generatePrepared
 apply RelCT.assoc
 exact RelCT.seq (two_post generateFront_ct (fun _ _ h =>front_done_ok h))
  ((generateBody_ct M).mono (fun _ _ h =>front_done_two h) (fun _ _ h =>h))

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure NativeState (q : FrontPublic) (rb : List Byte) (s : State) : Prop where
 scratch : Scr s q.body.scalar.p.B q.body.scalar.p.Z
 view : ContextView q.body.scalar.p.B q.body.scalar.p.Z q.body.scalar.p.ctx q.count q.body.scalar.p.k q.body.scalar.dom s
 domainSource : Src s q.body.scalar.p.B q.body.scalar.p.Z q.body.scalar.dp q.body.scalar.dom
 randomSource : Src s q.body.scalar.p.B q.body.scalar.p.Z q.rp rb
 rbLength : rb.length=q.body.scalar.p.k
 xArg : s.gpr .x0=q.body.scalar.p.src
 yArg : s.gpr .x2=q.body.yp
 domArg : s.gpr .x4=q.body.scalar.dp
 dlArg : s.gpr .x5=BitVec.ofNat 64 q.body.scalar.dl
 lenArg : s.gpr .x6=BitVec.ofNat 64 q.body.scalar.p.k
 randArg : s.gpr .x7=q.rp
 readB : s.mem.readW (s.sp+8#64) 64=q.body.scalar.p.B
 readCtx : s.mem.readW (s.sp+24#64) 64=q.body.scalar.p.ctx
 stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8
 stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8
 write : ∀ i<q.body.scalar.p.k,InRegions s.wr (q.body.scalar.p.src+BitVec.ofNat 64 i) 1
 status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom)
  (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) rb)=q.body.status

def NativeReady (q : FrontPublic) (s : State) : Prop := ∃ rb,NativeState q rb s

theorem native_front_ok {q : FrontPublic} {s : State} (h : NativeReady q s) :
 WP isa (.block Generate.entry) s (FrontReady q) := by
 obtain ⟨rb,h⟩:=h
 let p:=q.body.scalar.p
 have room : 256≤p.Z := by have :=p.room;dsimp only [slot,hdrBytes] at this;omega
 have count3 : 3≤q.count := by rw [context_words_count h.view.canonical];omega
 have domSize : p.k≤q.body.scalar.dom.length := by have :=q.body.scalar.shape;have :=q.body.scalar.domLength;dsimp only [p];omega
 have head (i : Nat) (hi : i<3) := context_header domSize (VG.Proof.Ffdh.domainValid_mod q.checked) h.view.canonical hi
 have head0 : word s.mem p.ctx 0=BitVec.ofNat 64 p.N := by simpa [word,off,p,q.policy] using head 0 (by decide)
 have head1 : word s.mem p.ctx 8=BitVec.ofNat 64 ((p.N+7)/8) := by simpa [word,off,p,q.policy] using head 1 (by decide)
 have head2 : word s.mem p.ctx 16=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N) := by simpa [word,off,p,q.policy] using head 2 (by decide)
 refine WP.mono (generateEntry_ok h.scratch room h.readB h.readCtx h.stackB h.stackCtx
  (fun i hi =>h.view.readable i (by omega)) (fun i hi =>h.view.outside i (by omega)) head0 head1 head2) ?_
 rintro t ⟨base,mem,frame,rest⟩
 have inscr : InScr p.B p.Z s.mem t.mem := InScr.of_outside frame (by omega)
 simp only [h.xArg,h.yArg,h.domArg,h.dlArg,h.lenArg,h.randArg] at mem
 have headers :=generationEntry_headers s.mem p.B p.src q.body.yp q.body.scalar.dp (BitVec.ofNat 64 q.body.scalar.dl)
  (BitVec.ofNat 64 p.k) q.rp p.ctx (BitVec.ofNat 64 p.N) (BitVec.ofNat 64 ((p.N+7)/8)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))
 change t.mem=generationMetadataMemory (generationSaveMemory s.mem p.B p.src q.body.yp q.body.scalar.dp
  (BitVec.ofNat 64 q.body.scalar.dl) (BitVec.ofNat 64 p.k) q.rp p.ctx) p.B (BitVec.ofNat 64 p.N)
  (BitVec.ofNat 64 ((p.N+7)/8)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)) at mem
 rw [←mem] at headers
 obtain ⟨ctx,domain,len,dl,x,y,rng,bits,bytes,rows⟩:=headers
 exact ⟨rb,h.scratch.congr rest.wr,base,h.view.after_inscr inscr rest,
  h.domainSource.congrK inscr rest,h.randomSource.congrK inscr rest,h.rbLength,
  ⟨ctx,x,len,bits,rows⟩,domain,dl,y,rng,bytes,
  fun i hi =>by rw [rest.wr];exact h.write i hi,h.status⟩

end VG.Proof.Ffdh.AArch64.Cached
