module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.DomainFacts
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecognize
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-! Checked domains provide every bound-scan premise, including its nonzero leading byte. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh (lead lead_lt lead_zero lead_nonzero)
open VG.Proof.Ffdh.KeyScalar (bnd)

theorem checked_bound_bits {k : Nat} {dom : List Byte} (positive : 0<k)
 (shape : dom.length=2*k ∨ dom.length=3*k) (valid : Spec.Ffdh.domainValid k dom=true) :
 Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))=
 8*((bnd k dom).length-lead (bnd k dom)-1)+
 Spec.RsaKeyGen.bitLength ((bnd k dom).getD (lead (bnd k dom)) 0).toNat := by
 have length := VG.Proof.Ffdh.KeyScalar.bnd_length shape
 have nonempty : bnd k dom≠[] := by intro h;rw [h] at length;simp at length;omega
 have modulus := VG.Proof.Ffdh.domainValid_mod valid
 simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at modulus
 dsimp only [Spec.Ffdh.domainOf] at modulus
 have bound := VG.Proof.Ffdh.KeyScalar.bound_bits (by omega : 1≤k) shape (fun _ => ⟨modulus.1.1.1,by omega⟩)
 rw [length,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (lead_lt nonempty),Option.getD_some]
 exact bound

theorem checked_bound_lead {k : Nat} {dom : List Byte} (positive : 0<k)
 (shape : dom.length=2*k ∨ dom.length=3*k) (valid : Spec.Ffdh.domainValid k dom=true) :
 let bs := bnd k dom
 lead bs<bs.length ∧ (∀ i<lead bs,bs.getD i 0=0#8) ∧ bs.getD (lead bs) 0≠0#8 := by
 dsimp only
 have length := VG.Proof.Ffdh.KeyScalar.bnd_length shape
 have nonempty : bnd k dom≠[] := by intro h;rw [h] at length;simp at length;omega
 have inside := lead_lt nonempty
 refine ⟨inside,?_,?_⟩
 · intro i hi
   obtain ⟨bound,zero⟩ := lead_zero (bs:=bnd k dom) i hi
   change (bnd k dom)[i]=0#8 at zero
   simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using zero
 · intro zero
   have last : ¬lead (bnd k dom)+1<(bnd k dom).length := by
    intro before
    have nz := lead_nonzero nonempty before
    have same : (bnd k dom).getD (lead (bnd k dom)) 0=(bnd k dom)[lead (bnd k dom)] := by
     simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some]
    exact nz (same.symm.trans zero)
   have bits := checked_bound_bits positive shape valid
   rw [zero] at bits
   have pos := scalarBound_positive valid
   have lengthPos : 0<Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) := by
    unfold Spec.RsaKeyGen.bitLength
    rw [ite_eq_right (by omega : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)≠0)]
    omega
   have tail : (bnd k dom).length-lead (bnd k dom)-1=0 := by omega
   rw [tail] at bits
   change Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))=0 at bits
   omega

theorem Source.bound {s : State} {domPtr : Addr} {dom : List Byte} {k dl : Nat}
 (source : Source domPtr dom s) (positive : 0<k) (length : dom.length=dl) (shape : dl=2*k ∨ dl=3*k) :
 Source (if dl=2*k then domPtr else off domPtr (2*k)) (bnd k dom) s := by
 unfold bnd
 by_cases three : dl=3*k
 · rw [ite_eq_left (by omega : dom.length=3*k),ite_eq_right (by omega : ¬dl=2*k)]
   exact (source.drop (2*k)).take k
 · rw [ite_eq_right (by omega : ¬dom.length=3*k),ite_eq_left (by omega : dl=2*k)]
   exact source.take k

theorem policyDomain_ok {s : State} {B domPtr : Addr} {Z k dl : Nat} {dom : List Byte}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<k) (size : k≤1024) (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid k dom=true)
 (pointer : word s.mem B (8*sDom)=domPtr) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (source : Source domPtr dom s)
 (outside : ∀ i<dom.length,8*sBits+8≤ofs B (domPtr+BitVec.ofNat 64 i))
 (records : PolicyTableAt B (s.syms Policy.tableSym) Policy.groups s) :
 WP isa Policy.recognize s fun t =>
 word t.mem B (8*sBits)=BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)) ∧
 Outside B (8*sBits) 8 s.mem t.mem ∧ Keep recordClobbers s t := by
 have shapeDom : dom.length=2*k ∨ dom.length=3*k := by omega
 have leadFacts := checked_bound_lead positive shapeDom valid
 have bits := checked_bound_bits positive shapeDom valid
 refine WP.mono (policyRecognize_ok scratch room base positive (by omega) shape domLength pointer length domainLength
  source outside (source.bound positive domLength shape) (VG.Proof.Ffdh.KeyScalar.bnd_length shapeDom)
  leadFacts.1 leadFacts.2.1 leadFacts.2.2 records) ?_
 rintro t ⟨width,frame,rest⟩
 rw [←bits,policyWidth_spec positive shapeDom (domain_normalized positive valid)] at width
 exact ⟨width,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
