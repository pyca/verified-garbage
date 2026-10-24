module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeNative
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyDomainTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MetadataTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ArithmeticTiming
import VerifiedGarbage.Proof.Framework.Omega

/-! Public inputs and staging predicates for the complete context initializer. -/
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
