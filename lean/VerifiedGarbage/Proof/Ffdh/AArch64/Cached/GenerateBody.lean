module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.RangeFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceEncoding
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Fail
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Finish
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.KeyStatus
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The complete post-sampling operation has the reviewed scalar/key status and exact outputs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

def generateBody (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq Generate.scalarRange (.ite (.zero .x .x9) Generate.fail
  (.seq (Comb.code mul) (.seq Generate.publicRange Generate.finish)))

theorem generateBody_ok (M : Mont) {p : Parameters} {s : State} {bs dom : List Byte} {dp yp : Addr} {dl : Nat}
 (start : Initial p bs s) (words : p.w=(p.k+7)/8) (positive : 0<p.k) (size : p.k<2^31)
 (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (domainSource : Src s p.B p.Z dp dom)
 (domain : word s.mem p.B (8*sDom)=dp) (domainLength : word s.mem p.B (8*sDL)=BitVec.ofNat 64 dl)
 (outputY : word s.mem p.B (8*sY)=yp)
 (bitsPositive : 0<p.N) (bitsBound : p.N≤8192) (scalarWidth : p.N≤8*p.k) (scalarBound : Spec.Rsa.os2ip bs<2^p.N)
 (table : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (writeX : ∀ i<p.k,InRegions s.wr (p.src+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<p.k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideY : ∀ i<p.k,p.Z≤ofs p.B (yp+BitVec.ofNat 64 i))
 (separate : ∀ i<p.k,p.k≤ofs yp (p.src+BitVec.ofNat 64 i)) :
 WP isa (generateBody M.mm) s fun t =>
 t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k dom) (Spec.Rsa.os2ip bs)) ∧
 (if Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k dom) (Spec.Rsa.os2ip bs)=1 then
  Spec.Rsa.bytesAt t.mem p.src p.k=Spec.Rsa.i2osp (Spec.Rsa.os2ip bs) p.k ∧
  Spec.Rsa.bytesAt t.mem yp p.k=Spec.Rsa.i2osp (Spec.Rsa.powMod p.G (Spec.Rsa.os2ip bs) p.P) p.k
 else Spec.Rsa.bytesAt t.mem p.src p.k=List.replicate p.k 0 ∧ Spec.Rsa.bytesAt t.mem yp p.k=List.replicate p.k 0) ∧
 Keep (.x0::mmRegs) s t := by
 let a := Spec.Ffdh.domainOf p.k dom
 let X := Spec.Rsa.os2ip bs
 have bsLength := start.reads.length
 have paramValid : Spec.Ffdh.parametersValid a=true := by
  have h := valid
  unfold Spec.Ffdh.domainValid at h
  simp only [Bool.and_eq_true] at h
  exact h.1
 have odd : p.P%2=1 := by
  have h := VG.Proof.Ffdh.domainValid_mod valid
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  rw [modulus]
  exact h.1.1.1
 have room256 : 256≤p.Z := by have := p.room;dsimp only [slot,hdrBytes] at this;omega
 have outsideX (i : Nat) (hi : i<p.k) : p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i) := start.reads.scalarOutside i (by omega)
 have length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k := bsLength ▸ start.controls.length
 have status := keyStatus_ranges paramValid X
 change Spec.Ffdh.keyStatus a X=(if 0<X ∧ X<Spec.Ffdh.scalarBound a then _ else 2) at status
 rw [←modulus,←generator] at status
 unfold generateBody
 rw [WP.seq_iff]
 refine WP.mono (scalarRange_ok start.good p.room words positive size shape domLength domainSource
  (source_src start.reads.source start.reads.scalarOutside) bsLength start.controls.source domain length domainLength
  (start.modulus.trans modulus) (by rw [←modulus];exact odd)) ?_
 rintro r ⟨goodR,_,flagR,frameR,restR⟩
 have startR := start.after_scalarRange goodR frameR restR
 have yR : word r.mem p.B (8*sY)=yp := (scalarFrame_header frameR (by decide) (by decide)).trans outputY
 have lenR : word r.mem p.B (8*sLen)=BitVec.ofNat 64 p.k := bsLength ▸ startR.controls.length
 by_cases accepted : 0<X ∧ X<Spec.Ffdh.scalarBound a
 · have condition : isa.eval (.zero .x .x9) r=some false := by
    rw [eval_zero,flagR,ite_eq_left accepted];decide
   have branch : WP isa (.seq (Comb.code M.mm) (.seq Generate.publicRange Generate.finish)) r fun t =>
    t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus a X) ∧
    (if Spec.Ffdh.keyStatus a X=1 then
     Spec.Rsa.bytesAt t.mem p.src p.k=Spec.Rsa.i2osp X p.k ∧
     Spec.Rsa.bytesAt t.mem yp p.k=Spec.Rsa.i2osp (Spec.Rsa.powMod p.G X p.P) p.k
    else Spec.Rsa.bytesAt t.mem p.src p.k=List.replicate p.k 0 ∧ Spec.Rsa.bytesAt t.mem yp p.k=List.replicate p.k 0) ∧
    Keep (.x0::mmRegs) s t := by
    rw [WP.seq_iff]
    refine WP.mono (comb_correct M startR bitsPositive bitsBound (bsLength ▸ size) (bsLength ▸ scalarWidth) scalarBound table) ?_
    rintro b ⟨stateB,valueB,controlsB,readsB,stableB,restB⟩
    have yB : word b.mem p.B (8*sY)=yp := (stableB sY (by decide) (by decide) (by decide) (by decide)).trans yR
    rw [WP.seq_iff]
    refine WP.mono (publicRange_ok stateB odd) ?_
    rintro c ⟨stateC,sameY,flagC,headerC,frameC,restC⟩
    let ok : Bool := decide (1<Spec.Rsa.powMod p.G X p.P ∧ Spec.Rsa.powMod p.G X p.P<p.P-1)
    have flag : word c.mem p.B (8*sTmp)=BitVec.ofNat 64 ok.toNat := by
     rw [headerC,flagC,valueB]
     exact (bit_decide (1<Spec.Rsa.powMod p.G X p.P ∧ Spec.Rsa.powMod p.G X p.P<p.P-1)).symm
    have readsC := readsB.after_inscr (InScr.of_frm frameC
     (fun r hr =>Nat.le_trans (publicRangeRanges_le _ r hr) p.room)) restC
    have xC : word c.mem p.B (8*sX)=p.src := (publicRangeFrame_header frameC (by decide) (by decide)).trans controlsB.source
    have yC : word c.mem p.B (8*sY)=yp := (publicRangeFrame_header frameC (by decide) (by decide)).trans yB
    have lenC : word c.mem p.B (8*sLen)=BitVec.ofNat 64 p.k :=
     (publicRangeFrame_header frameC (by decide) (by decide)).trans (bsLength ▸ controlsB.length)
    have sourceC := source_encoding readsC.source
    rw [bsLength] at sourceC
    have statusOk : Spec.Ffdh.keyStatus a X=(if ok then 1 else 3) := by
     rw [status,ite_eq_left accepted]
     simp only [ok,decide_eq_true_eq]
    have before := (restR.trans restB).trans restC
    refine WP.mono (finish_ok stateC.good p.room words positive size xC yC lenC flag
     (fun i hi =>by rw [before.wr];exact writeX i hi)
     (fun i hi =>by rw [before.wr];exact writeY i hi) outsideX outsideY separate) ?_
    rintro t ⟨ret,xT,yT,_,restT⟩
    rw [sourceC] at xT
    rw [sameY,valueB] at yT
    refine ⟨?_,?_,(before.trans restT).mono (by simp [mmRegs])⟩
    · rw [ret,statusOk]
      cases ok <;>rfl
    · rw [statusOk]
      cases h : ok
      · simpa only [h,ite_false,Bool.false_eq_true,show ¬(3:Nat)=1 by decide,i2osp_zero'] using And.intro xT yT
      · simpa only [h,ite_true] using And.intro xT yT
   obtain ⟨tr,t,run,post⟩ := branch
   exact ⟨_,t,.iteF condition run,post⟩
 · have condition : isa.eval (.zero .x .x9) r=some true := by
    rw [eval_zero,flagR,ite_eq_right accepted];decide
   have code := fail_ok goodR.scr room256 goodR.x0 positive size startR.controls.source yR lenR
    (fun i hi =>by rw [restR.wr];exact writeX i hi)
    (fun i hi =>by rw [restR.wr];exact writeY i hi) outsideX separate
   obtain ⟨tr,t,run,ret,xT,yT,_,restT⟩ := code
   refine ⟨_,t,.iteT condition run,?_,?_,(restR.trans restT).mono (by simp [mmRegs])⟩
   · rw [ret,status,ite_eq_right accepted]
   · rw [status,ite_eq_right accepted]
     exact ⟨xT,yT⟩

end VG.Proof.Ffdh.AArch64.Cached
