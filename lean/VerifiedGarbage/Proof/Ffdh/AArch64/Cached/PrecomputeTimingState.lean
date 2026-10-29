module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeNative
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MetadataTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyDomain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecognizeTiming
public import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeFieldFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTailTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InverseUnique

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
/-! Public inputs and staging predicates for the complete context initializer. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyDomainTiming.lean`, which only this module imported.
section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeFieldTiming.lean`, which only this module imported.
section

/-! Reuse the existing public modulus-load and R-squared timing proofs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeField_ct (M : Mont) : RelCT isa (Two PcM)
 (VG.Impl.Bignum.AArch64.seqs (pcLoadW++r2StepsPub M.mm)) (fun _ _ =>True) := by
 refine RelCT.seqs_append (by simp [pcLoadW,pcLoadWith]) (by simp [r2StepsPub]) (RelCT.seq
  (two_post (Ψ:=Pc3) (pcLoadW_ct.mono (fun _ _ h =>two_mono (fun _ _ h =>PcM.loadW h) h) (fun _ _ _ =>trivial)) ?_)
  ((pcR2_ct M).mono (fun _ _ h =>h) (fun _ _ _ =>trivial)))
 intro p s h
 have h':=h
 obtain ⟨scratch,base,room,small,large,_,length,modulus,source,nbLength,valid,_,_,span⟩:=h'
 exact WP.mono (pcLoadW_r2 scratch base room small large length modulus source span nbLength valid)
  (fun t ⟨mi,r2,frame,rest⟩ =>⟨mi,h.congr frame (fun r hr =>Nat.le_trans (pcLoadRanges_le _ r hr) room)
   (pcLoadRanges_fixed _) rest (by decide),r2⟩)

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ArithmeticTimingState.lean`, which only this module imported.
section

/-! Public modulus setup establishes the table builder's field without assuming prior scratch contents. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure ArithmeticPublic where
 table : TablePublic
 nb : List Byte
 value : Spec.Rsa.os2ip nb=table.p.P
 odd : table.p.P%2=1

def arithmeticPc (q : ArithmeticPublic) : PcPub :=
 ⟨q.table.p.B,q.table.p.Z,q.table.p.k,q.table.p.ctx,q.table.dom,q.nb⟩

def arithmeticTable (q : ArithmeticPublic) (mi : BitVec 64) : TablePublic :=
 {q.table with p:={q.table.p with mi:=mi}}

structure ArithmeticReady (q : ArithmeticPublic) (s : State) : Prop where
 pc : PcM (arithmeticPc q) s
 space : ContextSpace q.table.p s
 generator : GeneratorSource q.table.p (q.table.dom+BitVec.ofNat 64 q.table.p.k) q.table.bs s
 rows : word s.mem q.table.p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.table.p.N)

def ArithmeticDone (q : ArithmeticPublic) (s : State) : Prop :=∃ mi,TableReady (arithmeticTable q mi) s

theorem arithmeticField_done (M : Mont) {q : ArithmeticPublic} {s : State} (h : ArithmeticReady q s) :
 WP isa (seqs (VG.Impl.Rsa.AArch64.pcLoadW++VG.Impl.Rsa.AArch64.r2StepsPub M.mm)) s (ArithmeticDone q) := by
 obtain ⟨scratch,base,room,small,large,ctx,len,dom,source,nbLength,valid,_,_,span⟩:=h.pc
 dsimp only [arithmeticPc,PcPub.w,PcPub.N] at *
 have normalized :=(valid_facts valid small).2.2
 refine WP.mono (precomputeField_ok M scratch base room (by change 9≤q.table.p.k;change 64≤q.table.p.k at small;omega)
  q.table.size len dom source span nbLength (by rw [q.value];exact q.odd) normalized) ?_
 rintro t ⟨mi,good,modulus,inverse,r2,frame,rest⟩
 have field : FieldInitial (arithmeticTable q mi).p t :=by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [arithmeticTable,q.table.words] using good
  · simpa only [arithmeticTable,q.table.words,q.value] using modulus
  · simpa only [arithmeticTable,q.table.words] using inverse
  · simpa only [arithmeticTable,q.table.words,q.value] using r2
 have inscr : InScr q.table.p.B q.table.p.Z s.mem t.mem :=by
  apply precomputeField_inscr (w:=q.table.p.w) _ q.table.p.room
  simpa only [q.table.words] using frame
 have sourceT:=h.generator.after_inscr inscr rest
 have header (i : Nat) (lo : 16≤i) (hi : i<32) (different : i≠Public.sCnt) :=precomputeField_header frame lo hi different
 exact ⟨mi,⟨field,⟨(h.space.after rest).writable,h.space.outside⟩,
  ⟨sourceT.source,sourceT.length,sourceT.value,sourceT.separate⟩,
  (header sCtx (by decide) (by decide) (by decide)).trans ctx,
  (header sDom (by decide) (by decide) (by decide)).trans dom,
  (header sLen (by decide) (by decide) (by decide)).trans len⟩,
  (header sRows (by decide) (by decide) (by decide)).trans h.rows⟩

theorem arithmeticDone_two {s t : State} (h : Two ArithmeticDone s t) : Two TableReady s t := by
 obtain ⟨q,⟨a,hs⟩,⟨b,ht⟩,sp⟩:=h
 have same : a=b := imported_inverse_unique (p:=q.table.p) hs.field ht.field q.odd
 subst b
 exact ⟨arithmeticTable q a,hs,ht,sp⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ArithmeticTiming.lean`, which only this module imported.
section

/-! Compose public field setup with context serialization and the complete fixed-base table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64

theorem precomputeArithmetic_ct (M : Mont) : RelCT isa (Two ArithmeticReady)
 (.seq (seqs (VG.Impl.Rsa.AArch64.pcLoadW++VG.Impl.Rsa.AArch64.r2StepsPub M.mm))
  (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1])))) (fun _ _ =>True) :=
 RelCT.seq (two_post (two_map arithmeticPc (fun _ _ h =>h.pc) (precomputeField_ct M))
  (fun _ _ h =>arithmeticField_done M h))
  ((precomputeTail_ct M).mono (fun _ _ h =>arithmeticDone_two h) (fun _ _ h =>h))

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure PrecomputePublic where
 p : Parameters
 domPtr : Addr
 dom : List Byte
 dl : Nat
 table : Addr
 words : p.w=(p.k+7)/8
 small : 64≤p.k
 large : p.k≤1024
 shape : dl=2*p.k ∨ dl=3*p.k
 domLength : dom.length=dl
 checked : Spec.Ffdh.domainValid p.k dom=true
 modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p
 generator : p.G=(Spec.Ffdh.domainOf p.k dom).g
 policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom)

theorem precomputeBits (q : PrecomputePublic) : 0<q.p.N ∧ q.p.N≤8192 :=by
 rw [q.policy]
 exact ⟨generation_bits_positive q.checked,generation_bits_bound (by have :=q.small;omega) q.large⟩

def precomputeDomainPolicy (q : PrecomputePublic) : DomainPolicyPublic :=
 ⟨q.p.B,q.p.Z,q.domPtr,q.dom,q.p.k,q.dl,q.table,
  by have :=q.p.room;dsimp only [slot,hdrBytes] at this;omega,by have :=q.small;omega,q.large,q.shape,q.domLength,q.checked⟩

def precomputeMetadata (q : PrecomputePublic) : MetadataPublic :=
 ⟨q.p.B,q.p.Z,q.p.ctx,q.p.N,(precomputeDomainPolicy q).room,(precomputeBits q).1,(precomputeBits q).2⟩

def precomputeArithmetic (q : PrecomputePublic) : ArithmeticPublic :=by
 have facts :=(VG.Proof.Ffdh.domainValid_iff q.p.k q.dom).mp q.checked
 have reduced : q.p.G<q.p.P :=by rw [q.generator,q.modulus];have :=facts.2.1;omega
 have odd : q.p.P%2=1 :=by
  have mod:=VG.Proof.Ffdh.domainValid_mod q.checked
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at mod
  rw [q.modulus];exact mod.1.1.1
 exact ⟨⟨⟨q.p,q.domPtr,(q.dom.drop q.p.k).take q.p.k,q.words,by have :=q.small;omega,
  by have :=q.large;omega,reduced⟩,precomputeBits q⟩,q.dom.take q.p.k,q.modulus.symm,odd⟩

structure PrecomputeReady (q : PrecomputePublic) (s : State) : Prop where
 scratch : Scr s q.p.B q.p.Z
 space : ContextSpace q.p s
 output : Scr s q.p.ctx 24
 source : PublicSource q.p q.domPtr q.dom s
 span : InRegions (s.rd++s.wr) q.domPtr q.p.k
 context : s.gpr .x0=q.p.ctx
 domain : s.gpr .x2=q.domPtr
 domainLength : s.gpr .x3=BitVec.ofNat 64 q.dl
 length : s.gpr .x4=BitVec.ofNat 64 q.p.k
 base : s.gpr .x5=q.p.B
 records : PolicyTableAt q.p.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

structure PrecomputeSetup (q : PrecomputePublic) (s : State) : Prop where
 scratch : Scr s q.p.B q.p.Z
 space : ContextSpace q.p s
 output : Scr s q.p.ctx 24
 source : PublicSource q.p q.domPtr q.dom s
 span : InRegions (s.rd++s.wr) q.domPtr q.p.k
 base : s.gpr .x0=q.p.B
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 domain : word s.mem q.p.B (8*sDom)=q.domPtr
 domainLength : word s.mem q.p.B (8*sDL)=BitVec.ofNat 64 q.dl
 length : word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k

structure PrecomputeEntered (q : PrecomputePublic) (s : State) : Prop extends PrecomputeSetup q s where
 records : PolicyTableAt q.p.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

structure PrecomputePolicyDone (q : PrecomputePublic) (s : State) : Prop extends PrecomputeSetup q s where
 bits : word s.mem q.p.B (8*sBits)=BitVec.ofNat 64 q.p.N

theorem precomputeEntered_policy {q : PrecomputePublic} {s : State} (h : PrecomputeEntered q s) :
 DomainPolicyReady (precomputeDomainPolicy q) s :=
 ⟨h.scratch,h.base,h.domain,h.length,h.domainLength,h.source.toSource,
  fun i hi =>Nat.le_trans (by have :=q.p.room;dsimp only [slot,hdrBytes,sBits] at *;omega) (h.source.scratchOutside i hi),h.records,h.symbol⟩

theorem precomputePolicyDone_metadata {q : PrecomputePublic} {s : State} (h : PrecomputePolicyDone q s) :
 MetadataReady (precomputeMetadata q) s :=⟨h.scratch,h.base,h.context,h.bits⟩

end VG.Proof.Ffdh.AArch64.Cached
