module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateFront
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateBody
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Context import, the exact vetted entropy policy, and the complete cached operation compose. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def generatePrepared (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq importPrefix (.seq Generate.sample (generateBody mul))

theorem generatePrepared_ok (M : Mont) {p : Parameters} {s : State} {dom rb : List Byte} {dp rp yp : Addr} {dl count : Nat}
 (scratch : Scr s p.B p.Z) (base : s.gpr .x0=p.B) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (table : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (view : ContextView p.B p.Z p.ctx count p.k dom s)
 (domainSource : Src s p.B p.Z dp dom) (randomSource : Src s p.B p.Z rp rb) (rbLength : rb.length=p.k)
 (controls : Controls p.B p.src p.ctx p.k p.N s)
 (domain : word s.mem p.B (8*sDom)=dp) (domLen : word s.mem p.B (8*sDL)=BitVec.ofNat 64 dl)
 (y : word s.mem p.B (8*sY)=yp) (rand : word s.mem p.B (8*sRand)=rp)
 (bytes : word s.mem p.B (8*sBytes)=BitVec.ofNat 64 ((p.N+7)/8))
 (bitsPositive : 0<p.N) (bitsBound : p.N≤8192) (width : p.N≤8*p.k)
 (writeX : ∀ i<p.k,InRegions s.wr (p.src+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<p.k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<p.k,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (outsideY : ∀ i<p.k,p.Z≤ofs p.B (yp+BitVec.ofNat 64 i))
 (separateRand : ∀ i<p.k,∀ j<p.k,rp+BitVec.ofNat 64 i≠p.src+BitVec.ofNat 64 j)
 (separateDomain : ∀ i<dom.length,p.k≤ofs p.src (dp+BitVec.ofNat 64 i))
 (separateContext : ∀ i<8*count,p.k≤ofs p.src (p.ctx+BitVec.ofNat 64 i))
 (separateOutputs : ∀ i<p.k,p.k≤ofs yp (p.src+BitVec.ofNat 64 i)) :
 WP isa (generatePrepared M.mm) s fun t =>
 let a := Spec.Ffdh.domainOf p.k dom
 let x := Spec.Ffdh.vettedScalarOfOctets a rb
 t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus a x) ∧
 (if Spec.Ffdh.keyStatus a x=1 then
  Spec.Rsa.bytesAt t.mem p.src p.k=Spec.Rsa.i2osp x p.k ∧
  Spec.Rsa.bytesAt t.mem yp p.k=Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) p.k
 else Spec.Rsa.bytesAt t.mem p.src p.k=List.replicate p.k 0 ∧ Spec.Rsa.bytesAt t.mem yp p.k=List.replicate p.k 0) ∧
 Keep (.x0::mmRegs) s t := by
 unfold generatePrepared
 apply WP.assoc
 rw [WP.seq_iff]
 refine WP.mono (generateFront_ok scratch base words positive size shape domLength valid modulus generator policy table view
  domainSource randomSource rbLength controls domain domLen y rand bytes bitsPositive bitsBound width
  writeX outsideX separateRand separateDomain separateContext) ?_
 rintro u ⟨mi,start,value,sourceU,domainU,lenU,yU,restU⟩
 let q : Parameters := {p with mi:=mi}
 let bs := Spec.Rsa.bytesAt u.mem p.src p.k
 have valueU : Spec.Rsa.os2ip bs=Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k dom) rb := by
  unfold Spec.Ffdh.vettedScalarOfOctets
  rw [←policy]
  exact value
 have bound : Spec.Rsa.os2ip bs<2^q.N := by
  rw [value]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)
 refine WP.mono (generateBody_ok M start words positive size shape domLength valid modulus generator sourceU domainU lenU yU
  bitsPositive bitsBound width bound table
  (fun i hi =>by rw [restU.wr];exact writeX i hi)
  (fun i hi =>by rw [restU.wr];exact writeY i hi) outsideY separateOutputs) ?_
 rintro t ⟨status,outputs,restT⟩
 refine ⟨?_,?_,(restU.trans restT).mono (by simp [mmRegs])⟩
 · rw [valueU] at status
   exact status
 · rw [valueU] at outputs
   simpa only [q,generator,modulus] using outputs

end VG.Proof.Ffdh.AArch64.Cached
