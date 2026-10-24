module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratePrepared
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateEntry
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The complete native cached attempt, from its original register and stack arguments. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generateNative_ok (M : Mont) {p : Parameters} {s : State} {dom rb : List Byte} {dp rp yp : Addr} {dl count : Nat}
 (scratch : Scr s p.B p.Z) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (table : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (view : ContextView p.B p.Z p.ctx count p.k dom s)
 (domainSource : Src s p.B p.Z dp dom) (randomSource : Src s p.B p.Z rp rb) (rbLength : rb.length=p.k)
 (xArg : s.gpr .x0=p.src) (yArg : s.gpr .x2=yp) (domArg : s.gpr .x4=dp)
 (dlArg : s.gpr .x5=BitVec.ofNat 64 dl) (lenArg : s.gpr .x6=BitVec.ofNat 64 p.k) (randArg : s.gpr .x7=rp)
 (readB : s.mem.readW (s.sp+8#64) 64=p.B) (readCtx : s.mem.readW (s.sp+24#64) 64=p.ctx)
 (stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8) (stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8)
 (bitsPositive : 0<p.N) (bitsBound : p.N≤8192) (width : p.N≤8*p.k)
 (writeX : ∀ i<p.k,InRegions s.wr (p.src+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<p.k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<p.k,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (outsideY : ∀ i<p.k,p.Z≤ofs p.B (yp+BitVec.ofNat 64 i))
 (separateRand : ∀ i<p.k,∀ j<p.k,rp+BitVec.ofNat 64 i≠p.src+BitVec.ofNat 64 j)
 (separateDomain : ∀ i<dom.length,p.k≤ofs p.src (dp+BitVec.ofNat 64 i))
 (separateContext : ∀ i<8*count,p.k≤ofs p.src (p.ctx+BitVec.ofNat 64 i))
 (separateOutputs : ∀ i<p.k,p.k≤ofs yp (p.src+BitVec.ofNat 64 i)) :
 WP isa (Generate.code M.mm) s fun t =>
 let a := Spec.Ffdh.domainOf p.k dom
 let x := Spec.Ffdh.vettedScalarOfOctets a rb
 t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus a x) ∧
 (if Spec.Ffdh.keyStatus a x=1 then
  Spec.Rsa.bytesAt t.mem p.src p.k=Spec.Rsa.i2osp x p.k ∧
  Spec.Rsa.bytesAt t.mem yp p.k=Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) p.k
 else Spec.Rsa.bytesAt t.mem p.src p.k=List.replicate p.k 0 ∧ Spec.Rsa.bytesAt t.mem yp p.k=List.replicate p.k 0) ∧
 Keep (.x0::mmRegs) s t := by
 have room : 256≤p.Z := by have := p.room;dsimp only [slot,hdrBytes] at this;omega
 have count3 : 3≤count := by rw [context_words_count view.canonical];omega
 have domSize : p.k≤dom.length := by omega
 have head (i : Nat) (hi : i<3) := context_header domSize (VG.Proof.Ffdh.domainValid_mod valid) view.canonical hi
 have head0 : word s.mem p.ctx 0=BitVec.ofNat 64 p.N := by simpa [word,off,policy] using head 0 (by decide)
 have head1 : word s.mem p.ctx 8=BitVec.ofNat 64 ((p.N+7)/8) := by simpa [word,off,policy] using head 1 (by decide)
 have head2 : word s.mem p.ctx 16=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N) := by simpa [word,off,policy] using head 2 (by decide)
 unfold Generate.code
 rw [WP.seq_iff]
 refine WP.mono (generateEntry_ok scratch room readB readCtx stackB stackCtx
  (fun i hi =>view.readable i (by omega)) (fun i hi =>view.outside i (by omega)) head0 head1 head2) ?_
 rintro u ⟨baseU,memU,frameU,restU⟩
 have frame : InScr p.B p.Z s.mem u.mem := InScr.of_outside frameU (by omega)
 have headers := generationEntry_headers s.mem p.B p.src yp dp (BitVec.ofNat 64 dl) (BitVec.ofNat 64 p.k) rp p.ctx
  (BitVec.ofNat 64 p.N) (BitVec.ofNat 64 ((p.N+7)/8)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))
 simp only [xArg,yArg,domArg,dlArg,lenArg,randArg] at memU
 rw [←memU] at headers
 rcases headers with ⟨ctxU,domU,lenU,dlU,xU,yU,randU,bitsU,bytesU,rowsU⟩
 change WP isa (generatePrepared M.mm) u _
 refine WP.mono (generatePrepared_ok M (scratch.congr restU.wr) baseU words positive size shape domLength valid modulus generator policy table
  (view.after_inscr frame restU) (domainSource.congrK frame restU) (randomSource.congrK frame restU) rbLength
  ⟨ctxU,xU,lenU,bitsU,rowsU⟩ domU dlU yU randU bytesU bitsPositive bitsBound width
  (fun i hi =>by rw [restU.wr];exact writeX i hi)
  (fun i hi =>by rw [restU.wr];exact writeY i hi) outsideX outsideY separateRand separateDomain separateContext separateOutputs) ?_
 rintro t ⟨status,outputs,restT⟩
 exact ⟨status,outputs,(restU.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
