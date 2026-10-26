module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyDomain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecognizeTiming
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

/-! Checked public domains discharge all leading-zero and recognition timing premises. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh (lead)
open VG.Proof.Ffdh.KeyScalar (bnd)

structure DomainPolicyPublic where
 B : Addr
 Z : Nat
 src : Addr
 dom : List Byte
 k : Nat
 dl : Nat
 table : Addr
 room : 256≤Z
 positive : 0<k
 size : k≤1024
 shape : dl=2*k ∨ dl=3*k
 domLength : dom.length=dl
 checked : Spec.Ffdh.domainValid k dom=true

structure DomainPolicyReady (q : DomainPolicyPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 pointer : word s.mem q.B (8*sDom)=q.src
 length : word s.mem q.B (8*sLen)=BitVec.ofNat 64 q.k
 domainLength : word s.mem q.B (8*sDL)=BitVec.ofNat 64 q.dl
 source : Source q.src q.dom s
 outside : ∀ i<q.dom.length,8*sBits+8≤ofs q.B (q.src+BitVec.ofNat 64 i)
 records : PolicyTableAt q.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

def domainRecognize (q : DomainPolicyPublic) : RecognizePublic := by
 have shape : q.dom.length=2*q.k ∨ q.dom.length=3*q.k :=by have :=q.domLength;have :=q.shape;omega
 have leadFacts:=checked_bound_lead q.positive shape q.checked
 exact {
  B:=q.B,Z:=q.Z,dom:=q.src,k:=q.k,dl:=q.dl,bs:=bnd q.k q.dom,L:=lead (bnd q.k q.dom),room:=q.room,
  positive:=q.positive,size:=by have :=q.size;omega,shape:=q.shape,length:=VG.Proof.Ffdh.KeyScalar.bnd_length shape,
  inside:=leadFacts.1,zeros:=leadFacts.2.1,nonzero:=leadFacts.2.2,
  domBytes:=q.dom,table:=q.table,domLength:=q.domLength,small:=by have :=q.size;omega}

theorem domainRecognize_ready {q : DomainPolicyPublic} {s : State} (h : DomainPolicyReady q s) :
 RecognizeReady (domainRecognize q) s := by
 refine ⟨⟨h.scratch,h.base,h.pointer,h.length,h.domainLength,?_⟩,h.source,h.outside,h.records,h.symbol⟩
 change Source (if q.dl=2*q.k then q.src else off q.src (2*q.k)) (bnd q.k q.dom) s
 exact h.source.bound q.positive q.domLength q.shape

theorem policyDomain_ct : RelCT isa (Two DomainPolicyReady) Policy.recognize (fun _ _ =>True) :=
 two_map domainRecognize (fun _ _ h =>domainRecognize_ready h) policyRecognize_ct

end VG.Proof.Ffdh.AArch64.Cached
