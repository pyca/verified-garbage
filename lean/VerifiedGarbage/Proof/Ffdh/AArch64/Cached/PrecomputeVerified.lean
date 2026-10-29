module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeSat
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeInput
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTimingState
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeEntryTiming

import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
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
    omega
   rw [count] at canonical
   rw [canonical]
   apply VG.Proof.Ffdh.generationPrecompute_eq
   · have shape :=g.shape
     have length : (precomputeDomain s).length=(s.gpr .x3).toNat :=by simp only [precomputeDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range]
     change (s.gpr .x4).toNat≤(precomputeDomain s).length
     omega
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
 have domSize : q.p.k≤q.dom.length :=by have :=q.shape;have :=q.domLength;omega
 have nbLength : (q.dom.take q.p.k).length=q.p.k :=by simp only [List.length_take];omega
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
     exact space.writable i (by omega)
   · intro i hi
     change i<16*((q.p.k+7)/8) at hi
     rw [←q.words] at hi
     exact space.outside i (by omega)
   · rw [rest.rd,rest.wr];exact h.span
 · exact ⟨space.writable,space.outside⟩
 · exact source.generator (by have :=q.shape;have :=q.domLength;omega) q.generator

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
