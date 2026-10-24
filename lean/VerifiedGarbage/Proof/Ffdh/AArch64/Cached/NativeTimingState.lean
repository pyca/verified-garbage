module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateFrontTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateEntry
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The cached attempt's public calling convention and immutable input geometry. -/
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
