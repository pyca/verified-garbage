module

public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.AttemptRun
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptSat
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeSat
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeContract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptInput
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyConsts
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTimingState
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeEntryTiming
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Contract
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.CT
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Sat
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Correct
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont

/-! ### `Ffdh.AArch64.Cached.AttemptVerified`, which only this module used -/

section

/-! Cached native generation is correct, constant time, ABI preserving, and satisfiable. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Spec.Ffdh

theorem attempt_implies : attemptContract.Implies (Proof.Ffdh.cachedGenerateKeyContract abi) where
 pre:=fun _ h =>attempt_shared_pre h
 post:=by
  sig_implies_post [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,generateKeySig,abi,argRegs,
   attemptContract,attemptPost,stackArgs_five,List.append_eq]
 pub:=by
  rintro s t _ _ h
  sig_pub [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,generateKeySig,abi,argRegs,attemptContract,attemptPub,
   stackArgs_five,List.append_eq] at h
  simp only [List.getD_cons_succ,List.getD_cons_zero] at h
  obtain ⟨sp,leak,r0,r1,r2,r3,r4,r5,r6,r7,a0,a1,a2,a3,a4⟩:=h
  refine ⟨?_,sp,by rw [stackArgs_five,stackArgs_five,a0,a1,a2,a3,a4],?_⟩
  · simp only [argRegs,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨r0,r1,r2,r3,r4,r5,r6,r7⟩
  · unfold attemptLeak;exact leak
 sat:=attempt_shared_sat

theorem attempt_verified (M : Mont) : Verified target (Generate.code M.mm) (Proof.Ffdh.cachedGenerateKeyContract abi) :=by
 refine Verified.of_correct (k:=attemptContract) ?_ (attempt_constantTime M) attempt_implies
 intro s h
 obtain ⟨trace,t,run,preserved,post⟩:=attempt_correct M h
 exact ⟨trace,t,run,preserved,post⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PrecomputeVerified`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeInput`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeGeometry`, which only this module used -/

section

/-! The reviewed initializer buffers and constant regions supply the native geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure PrecomputeGeometry (s : State) : Prop where
 small : 64≤(s.gpr .x4).toNat
 large : (s.gpr .x4).toNat≤1024
 shape : (s.gpr .x3).toNat=2*(s.gpr .x4).toNat ∨ (s.gpr .x3).toNat=3*(s.gpr .x4).toNat
 count : (s.gpr .x1).toNat=3+34*(((s.gpr .x4).toNat+7)/8)
 room : slot (((s.gpr .x4).toNat+7)/8) 8≤(s.gpr .x6).toNat*8
 scratch : Scr s (s.gpr .x5) ((s.gpr .x6).toNat*8)
 context : Scr s (s.gpr .x0) ((s.gpr .x1).toNat*8)
 source : Src s (s.gpr .x5) ((s.gpr .x6).toNat*8) (s.gpr .x2) (precomputeDomain s)
 domainOutside : ∀ i<(precomputeDomain s).length,(s.gpr .x1).toNat*8≤ofs (s.gpr .x0) (s.gpr .x2+BitVec.ofNat 64 i)
 contextOutside : ∀ i<(s.gpr .x1).toNat*8,(s.gpr .x6).toNat*8≤ofs (s.gpr .x5) (s.gpr .x0+BitVec.ofNat 64 i)
 span : InRegions (s.rd++s.wr) (s.gpr .x2) (s.gpr .x4).toNat
 checked : Spec.Ffdh.domainValid (s.gpr .x4).toNat (precomputeDomain s)=true
 constants : ConstsOk Policy.tableConsts 0 s

theorem precompute_geometry {s : State} (h : precomputePre s) : PrecomputeGeometry s :=by
 obtain ⟨plain,constants⟩:=h
 simp only [precomputePlainPre,stripConsts_gpr,stripConsts_wr] at plain
 obtain ⟨rd,wr,dCD,dCS,dDS,wC,wD,wS,⟨small,large⟩,shape,count,sLen,checked⟩:=plain
 change s.rd.take (s.rd.length-Policy.tableConsts.length)=[⟨s.gpr .x2,(s.gpr .x3).toNat⟩] at rd
 change (s.gpr .x3).toNat=2*(s.gpr .x4).toNat ∨ (s.gpr .x3).toNat=3*(s.gpr .x4).toNat at shape
 have member : (⟨s.gpr .x2,(s.gpr .x3).toNat⟩ : Region)∈s.rd :=by
  apply List.mem_of_mem_take
  rw [rd];simp
 have scratch : Scr s (s.gpr .x5) ((s.gpr .x6).toNat*8) :=Scr.of_mem (by rw [wr];simp) wS
 have context : Scr s (s.gpr .x0) ((s.gpr .x1).toNat*8) :=Scr.of_mem (by rw [wr];simp) wC
 have countEq : (s.gpr .x1).toNat=3+34*(((s.gpr .x4).toNat+7)/8) :=by
  simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,Spec.Rsa.precomputedWords,
   Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Spec.Rsa.modulusWords] at count
  omega_using [count]
 have room : slot (((s.gpr .x4).toNat+7)/8) 8≤(s.gpr .x6).toNat*8 :=by
  unfold Spec.Rsa.scratchWords at sLen
  dsimp only [slot,hdrBytes];omega_using [small, sLen]
 have domLength : (precomputeDomain s).length=(s.gpr .x3).toNat :=by simp only [precomputeDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range]
 refine ⟨small,large,shape,countEq,room,scratch,context,src_of_region (List.mem_append_left _ member) (by omega_using []) dDS,?_,?_,?_,checked,constants⟩
 · intro i hi
   exact out_scr dCD.symm (contains_byte _ (by rw [domLength] at hi;exact hi) (by omega_using []))
 · intro i hi
   exact out_scr dCS (contains_byte _ hi (by omega_using [wC]))
 · refine ⟨⟨s.gpr .x2,(s.gpr .x3).toNat⟩,List.mem_append_left _ member,?_⟩
   have span :=Offset.contains_base (s.gpr .x2) (d:=0) (n:=(s.gpr .x4).toNat) (k:=(s.gpr .x3).toNat) (by omega_using [shape]) (by decide)
   simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using span

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The initializer ABI establishes its complete native input predicate. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

def precomputeNativeParameters (s : State) (g : PrecomputeGeometry s) : Parameters :=
 checkedParameters (s.gpr .x5) (s.gpr .x0) (s.gpr .x0) ((s.gpr .x6).toNat*8)
  (s.gpr .x4).toNat (precomputeDomain s) g.room g.small g.large g.checked

def precomputeInputPublic (s : State) (g : PrecomputeGeometry s) : PrecomputePublic :=
 ⟨precomputeNativeParameters s g,s.gpr .x2,precomputeDomain s,(s.gpr .x3).toNat,s.syms Policy.tableSym,
  rfl,g.small,g.large,g.shape,by simp only [precomputeDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range],
  g.checked,rfl,rfl,rfl⟩

theorem precompute_input_ready {s : State} (g : PrecomputeGeometry s) :
 PrecomputeReady (precomputeInputPublic s g) s :=by
 have space : ContextSpace (precomputeNativeParameters s g) s :=by
  constructor
  · intro i hi
    apply g.context.st
    change 8*i+8≤(s.gpr .x1).toNat*8
    change i<3+34*(((s.gpr .x4).toNat+7)/8) at hi
    rw [g.count];omega_using [hi]
  · intro i hi
    apply g.contextOutside
    change i<8*(3+34*(((s.gpr .x4).toNat+7)/8)) at hi
    rw [g.count];omega_using [hi]
 have output : Scr s (s.gpr .x0) 24 :=by
  have h:=g.context.sub (o:=0) (n:=24) (by rw [g.count];omega_using []) (by decide)
  simpa only [off,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
 have source : PublicSource (precomputeNativeParameters s g) (s.gpr .x2) (precomputeDomain s) s :=by
  refine ⟨src_source g.source,g.source.out,?_⟩
  intro i hi
  change 8*(3+34*(((s.gpr .x4).toNat+7)/8))≤_
  change 8*(3+34*(((s.gpr .x4).toNat+7)/8))≤ofs (s.gpr .x0) (s.gpr .x2+BitVec.ofNat 64 i)
  rw [←g.count];simpa only [Nat.mul_comm] using g.domainOutside i hi
 exact ⟨g.scratch,space,output,source,g.span,rfl,rfl,(ofNat_toNat64 _).symm,(ofNat_toNat64 _).symm,rfl,
  policyConsts_table g.constants g.scratch (by have :=g.room;dsimp only [slot,hdrBytes] at this;omega_using [this]),rfl⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The complete native initializer satisfies the reviewed ABI and public-table convention. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeCorrect.lean`, which only this module imported.
section

/-! The native initializer returns the exact canonical reviewed context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

theorem precompute_correct (M : Mont) {s : State} (pre : precomputePre s) :
 WP isa (Precompute.code M.mm) s fun t =>abiPreserved s t ∧ precomputePost s t :=by
 let g:=precompute_geometry pre
 let q:=precomputeInputPublic s g
 have ns:=precompute_input_ready g
 have records : PolicyTableAt q.p.B (s.syms Policy.tableSym) Policy.groups s :=by
  rw [ns.symbol];exact ns.records
 refine WP.mono (precomputeNative_ok M ns.scratch ns.space ns.output ns.source ns.span
  q.words q.small q.large q.shape q.domLength q.checked q.modulus q.generator q.policy
  ns.context ns.domain ns.domainLength ns.length ns.base records) ?_
 rintro t ⟨status,canonical,frame,rest⟩
 refine ⟨abiPreserved_of_keep rest,?_,?_⟩
 · change (t.gpr .x0).setWidth 32=1#32
   rw [status];rfl
 · change Spec.Ffdh.generationPrecompute (s.gpr .x4).toNat (precomputeDomain s)=
    some (Spec.Rsa.wordsAt t.mem (s.gpr .x0) (s.gpr .x1).toNat)
   rw [g.count]
   change Spec.Rsa.wordsAt t.mem (s.gpr .x0) (Spec.Ffdh.generationPrecomputedWords (s.gpr .x4).toNat)=_ at canonical
   have count : Spec.Ffdh.generationPrecomputedWords (s.gpr .x4).toNat=3+34*(((s.gpr .x4).toNat+7)/8) :=by
    simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,Spec.Rsa.precomputedWords,
     Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Spec.Rsa.modulusWords]
    omega_using []
   rw [count] at canonical
   rw [canonical]
   apply VG.Proof.Ffdh.generationPrecompute_eq
   · have shape :=g.shape
     have length : (precomputeDomain s).length=(s.gpr .x3).toNat :=by simp only [precomputeDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range]
     change (s.gpr .x4).toNat≤(precomputeDomain s).length
     omega_using [shape, length]
   · exact VG.Proof.Ffdh.domainValid_mod g.checked

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeMetadataTiming.lean`, which only this module imported.
section

/-! Metadata writes preserve the domain and establish the public arithmetic setup. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeMetadata_arithmetic {q : PrecomputePublic} {s : State} (h : PrecomputePolicyDone q s) :
 WP isa Policy.metadata s (ArithmeticReady (precomputeArithmetic q)) := by
 have room :=(precomputeDomainPolicy q).room
 have bits:=precomputeBits q
 refine WP.mono (metadata_ok h.scratch room h.output h.base h.context h.bits bits.1 bits.2) ?_
 rintro t ⟨mem,rest⟩
 have frame : PublicFrame q.p s.mem t.mem :=by rw [mem];exact metadataMemory_frame _ q.p _
 have source:=h.source.after frame rest
 have controls:=metadataMemory_controls h.space h.scratch q.p.N
 rw [←mem] at controls
 have header (i : Nat) (hi : i<32) (notBytes : i≠sBytes) (notRows : i≠sRows) :=controls.2.2 i hi notBytes notRows
 have space:=h.space.after rest
 have domSize : q.p.k≤q.dom.length :=by have :=q.shape;have :=q.domLength;omega_arith
 have nbLength : (q.dom.take q.p.k).length=q.p.k :=by simp only [List.length_take];omega_using [domSize]
 refine ⟨?_,?_,?_,controls.2.1⟩
 · change PcM (⟨q.p.B,q.p.Z,q.p.k,q.p.ctx,q.domPtr,q.dom.take q.p.k⟩ : PcPub) t
   refine ⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,
    by change slot ((q.p.k+7)/8) 8≤q.p.Z;rw [←q.words];exact q.p.room,q.small,q.large,
    (header sCtx (by decide) (by decide) (by decide)).trans h.context,
    (header sLen (by decide) (by decide) (by decide)).trans h.length,
    (header sDom (by decide) (by decide) (by decide)).trans h.domain,
    (source.take q.p.k).toSrc,nbLength,VG.Proof.Ffdh.domainValid_mod q.checked,?_,?_,?_⟩
   · intro i hi
     change i<2*((q.p.k+7)/8) at hi
     rw [←q.words] at hi
     exact space.writable i (by omega_using [hi])
   · intro i hi
     change i<16*((q.p.k+7)/8) at hi
     rw [←q.words] at hi
     exact space.outside i (by omega_using [hi])
   · rw [rest.rd,rest.wr];exact h.span
 · exact ⟨space.writable,space.outside⟩
 · exact source.generator (by have :=q.shape;have :=q.domLength;omega_arith) q.generator

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeNativeTiming.lean`, which only this module imported.
section

/-! The complete native public initializer is constant time with respect to all non-public memory. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64

theorem precomputeNative_ct (M : Mont) : RelCT isa (Two PrecomputeReady) (Precompute.code M.mm) (fun _ _ =>True) := by
 unfold Precompute.code
 refine RelCT.seq (two_post precomputeEntry_ct (fun _ _ h =>precomputeEntry_entered h)) ?_
 refine RelCT.seq (two_post (two_map precomputeDomainPolicy (fun _ _ h =>precomputeEntered_policy h) policyDomain_ct)
  (fun _ _ h =>precomputePolicy_metadata h)) ?_
 exact RelCT.seq (two_post (two_map precomputeMetadata (fun _ _ h =>precomputePolicyDone_metadata h) metadata_ct)
  (fun _ _ h =>precomputeMetadata_arithmetic h))
  (two_map precomputeArithmetic (fun _ _ h =>h) (precomputeArithmetic_ct M))

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeTiming.lean`, which only this module imported.
section

/-! Public ABI inputs determine every initializer branch and address. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

theorem precomputePub_input {s t : State} (gs : PrecomputeGeometry s) (gt : PrecomputeGeometry t)
 (h : precomputePub s t) : precomputeInputPublic s gs=precomputeInputPublic t gt ∧ s.sp=t.sp :=by
 obtain ⟨sp,dom,r0,r1,r2,r3,r4,r5,r6,symbol⟩:=h
 have bytes : precomputeDomain s=precomputeDomain t :=by
  have recover:=congrArg (List.map (BitVec.ofNat 8)) dom
  simpa only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id'] using recover
 refine ⟨?_,sp⟩
 unfold precomputeInputPublic precomputeNativeParameters checkedParameters
 simp only [r0,r2,r3,r4,r5,r6,bytes,symbol]

theorem precompute_constantTime (M : Mont) : ConstantTime isa precomputePre precomputePub (Precompute.code M.mm) :=by
 intro s t ts tt u v hs ht hp es et
 let gs:=precompute_geometry hs
 let gt:=precompute_geometry ht
 have publicInfo:=precomputePub_input gs gt hp
 have first:=precompute_input_ready gs
 have second : PrecomputeReady (precomputeInputPublic s gs) t :=by
  rw [publicInfo.1];exact precompute_input_ready gt
 exact ((precomputeNative_ct M) _ _ _ _ _ _ ⟨precomputeInputPublic s gs,first,second,publicInfo.2⟩ es et).1

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Spec.Ffdh

theorem precompute_implies : precomputeContract.Implies (generationPrecomputeContract (abi.withConsts Policy.tableConsts)) where
 pre:=fun _ h=>precompute_shared_pre h
 post:=by
  intro s t _ h
  apply post_consts.mpr
  have shared : ∀ s t,True → precomputeContract.post s t → (generationPrecomputeContract abi).post s t :=by
   sig_implies_post [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs,precomputeContract,precomputePost]
  exact shared s t True.intro h
 pub:=by
  rintro s t _ _ h
  obtain ⟨plain,symbols⟩:=pub_consts.mp h
  sig_pub [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs] at plain
  obtain ⟨sp,dom,r0,r1,r2,r3,r4,r5,r6⟩:=plain
  exact ⟨sp,dom,r0,r1,r2,r3,r4,r5,r6,symbols _ List.mem_cons_self⟩
 sat:=precompute_shared_sat

theorem precompute_verified (M : Mont) : Verified target (Precompute.code M.mm)
 (generationPrecomputeContract (abi.withConsts Policy.tableConsts)) :=by
 refine Verified.of_correct (k:=precomputeContract) ?_ (precompute_constantTime M) precompute_implies
 intro s h
 obtain ⟨trace,t,run,preserved,post⟩:=precompute_correct M h
 exact ⟨trace,t,run,preserved,post⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.SearchProof.Verified`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.SearchProof.Implies`, which only this module used -/

section

/-! # The key search's contract is its shared callable contract (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Spec.Ffdh

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,stackArg s 5,stackArg s 6] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 56 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 56 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact h

theorem key_implies_pre (s : State) (h : (cachedKeySearchContract abi 64).pre s) : keyContract.pre s := by
  sig_pre [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads,inContext, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_seven,
    List.append_eq] at h
  sig_pre [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads,inContext, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_seven,
    List.append_eq] at h
  sig_split h
  sig_reduce [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, stackBelow, keyContract, keyPre,
    inReads,inContext, inWrites, inX, inY, inUsed, inDom, inRand, inScr, inCtl, inArgs, stackArgs_seven,
    List.append_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.pairwise_cons, List.Pairwise.nil, and_true, false_implies,
    implies_true]
  sig_and_intros
  sig_close
  all_goals first
    | (intro x hx; cases hx)
    | exact True.intro
    | with_reducible assumption
    | with_reducible rfl
    | omega
    | with_reducible exact Region.Disjoint.symm ‹_›
    | exact args_nowrap ‹_›

theorem key_implies_post : ∀ s t, (cachedKeySearchContract abi 64).pre s →
    keyContract.post s t → (cachedKeySearchContract abi 64).post s t := by
  sig_implies_post [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, keyContract, keyPost, keyResult,
    keyRand, keyA, keyDom, keyLen, keyRetries, stackArgs_seven, List.append_eq, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem key_implies_pub (s t : State) (_hs : (cachedKeySearchContract abi 64).pre s)
    (_ht : (cachedKeySearchContract abi 64).pre t) (h : (cachedKeySearchContract abi 64).pub s t) :
    keyContract.pub s t := by
  sig_pub [cachedKeySearchContract, cachedKeySearchSig,keySearchSig,Spec.Ffdh.generationContextAt, abi, argRegs, stackArgs_seven, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4,a5,a6⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .x5) (t.gpr .x6).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r6]
  have hl2 : (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt s.mem (stackArg s 4) 4)).length =
      (List.map (fun x => x.toNat) (Spec.Rsa.wordsAt t.mem (stackArg t 4) 4)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range]
  obtain ⟨hab, hst⟩ := List.append_inj hleak (by simp only [List.length_append, hl1, hl2])
  obtain ⟨hdom, hw⟩ := List.append_inj hab hl1
  refine ⟨hsp, ?_, fun j hj => ?_,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hdom,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, hst⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ =>exact a5
  | 6, _ =>exact a6
  | _ + 7, h =>omega

theorem key_implies : keyContract.Implies (cachedKeySearchContract abi 64) where
  pre := key_implies_pre
  post := key_implies_post
  pub := key_implies_pub
  sat:=key_sat

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end


/-! The complete cached rejection search satisfies the reviewed public API. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof
open VG VG.AArch64

theorem key_verified (a : Attempt) :
 Verified target (Impl.Ffdh.AArch64.Cached.Search.code a.call) (Spec.Ffdh.cachedKeySearchContract abi stackUse) :=
 Verified.of_correct (key_correct a) (key_constantTime a) key_implies

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end


/-! The public cached APIs share the existing eight-limb product and dedicated square backend. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64

def cachedAttempt : SearchProof.Attempt :=⟨Mont.productEight,by decide +kernel⟩

def cachedSearch : Prog isa :=Impl.Ffdh.AArch64.Cached.Search.code cachedAttempt.call

theorem cachedSearch_verified : Verified target cachedSearch (Spec.Ffdh.cachedKeySearchContract abi 64) :=
 SearchProof.key_verified cachedAttempt

end VG.Proof.Ffdh.AArch64.Cached
