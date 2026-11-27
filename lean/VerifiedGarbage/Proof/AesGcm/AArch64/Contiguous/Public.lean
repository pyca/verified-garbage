module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Dispatch
public import VerifiedGarbage.Spec.Gcm.Contiguous
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.Rounds
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Contract

/-! The platform-independent signature supplies one writable region on pointer
equality, and two separate permissions otherwise. Both feed the same proof. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous
open VG VG.AArch64 VG.Impl.AesGcm.AArch64.Contiguous

abbrev publicContract := Spec.Gcm.sealContiguousWithPowersContract abi 2640

theorem public_pre {s : State} (h : publicContract.pre s) : (leafContract Guard.any).pre s := by
  by_cases eq : s.gpr .x6=s.gpr .x7
  all_goals
    sig_pre [Sig.bufs.eq_7,Sig.lists.eq_7,Sig.descs.eq_7,Sig.alignedBufs.eq_7,
      publicContract,Spec.Gcm.sealContiguousWithPowersContract,Spec.Gcm.sealContiguousAuxSig,
      Spec.Gcm.sealContiguousSig,Spec.Gcm.withPowersParam,Spec.Gcm.sealWithPowersPre,Spec.Gcm.sealPre,
      abi,argRegs,Gather.stackArgs_three,List.cons_append,List.nil_append] at h
    simp only [eq,↓reduceIte] at h
    simp [Sig.pairFacts,Sig.conj,List.filterMap_cons,and_assoc] at h
  case pos =>
    obtain ⟨room,top,rd,wr,kd,kt,nd,nt,ad,atg,dt,dp,da,_,_,sk,sn,sa,sd,st,spw,_,bk,bn,ba,bd,bt,_,rounds,pow⟩ := h
    have ed : srcR s = dstR s := by simp only [srcR,dstR,eq]
    refine ⟨⟨?_,?_,kd,kt,nd,nt,ad,atg,.inr eq,ed ▸ dt,dt,da,?_,?_,room,by omega,rounds⟩,
      ⟨?_,dp.symm,spw.symm,pow⟩,trivial⟩
    · apply Covers.of_mem
      simp [rd,wr,Gather.kR,Gather.nR,Gather.aR,srcR,callerArgs,eq,Gather.K,Gather.Nn,Gather.NL,Gather.Ad,Gather.AL]
    · apply Covers.of_mem
      simp [wr,dstR,tagR]
    · simpa only [externalRegions,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true,ed] using
        And.intro sk ⟨sn,sa,sd,sd,st⟩
    · simp only [externalRegions,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true,ed]
      exact ⟨by change (s.gpr .x0).toNat + 256 ≤ 2^64; omega,bn,ba,bd,bd,by change (stackArg s 1).toNat +16 ≤2^64; omega⟩
    · apply Covers.of_mem
      simp [Prepared.powerR,rd,wr]
  case neg =>
    obtain ⟨room,top,rd,wr,kd,kt,nd,nt,ad,atg,sd,st,dt,dp,da,_,_,sk,sn,sa,ss,sds,sts,spw,_,bk,bn,ba,bs,bd,bt,_,rounds,pow⟩ := h
    refine ⟨⟨?_,?_,kd,kt,nd,nt,ad,atg,.inl sd,st,dt,da,?_,?_,room,by omega,rounds⟩,
      ⟨?_,dp.symm,spw.symm,pow⟩,trivial⟩
    · apply Covers.of_mem
      simp [rd,wr,Gather.kR,Gather.nR,Gather.aR,srcR,callerArgs,Gather.K,Gather.Nn,Gather.NL,Gather.Ad,Gather.AL]
    · apply Covers.of_mem
      simp [wr,dstR,tagR]
    · simpa only [externalRegions,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true] using
        And.intro sk ⟨sn,sa,ss,sds,sts⟩
    · simp only [externalRegions,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true]
      exact ⟨by change (s.gpr .x0).toNat + 256 ≤ 2^64; omega,bn,ba,bs,bd,by change (stackArg s 1).toNat +16 ≤2^64; omega⟩
    · apply Covers.of_mem
      simp [Prepared.powerR,rd,wr]

theorem public_post {s t : State} (h : result s t) : publicContract.post s t := by
  sig_post [publicContract,Spec.Gcm.sealContiguousWithPowersContract,Spec.Gcm.sealContiguousAuxSig,
    Spec.Gcm.sealContiguousSig,Spec.Gcm.withPowersParam,Spec.Gcm.sealContiguousPost,abi,argRegs,
    Gather.stackArgs_three,List.cons_append,List.nil_append]
  intro key hk
  obtain ⟨cipher,hash,_⟩ := Proof.AesGcm.keyRounds_ctx hk
  unfold result at h
  rwa [cipher,hash,← Spec.Gcm.encrypt_eq] at h

theorem public_pub {a b : State} (h : publicContract.pub a b) : (leafContract Guard.any).pub a b := by
  have arg (i : Nat) := h.2.1 i
  have sp := h.1.1
  have dit := h.1.2
  refine ⟨⟨arg 0 (by decide),arg 1 (by decide),arg 2 (by decide),
    arg 3 (by decide),arg 4 (by decide),arg 5 (by decide),
    arg 6 (by decide),arg 7 (by decide),sp,?_⟩,dit⟩
  intro i hi
  have idx : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases idx with rfl|rfl|rfl
  · exact arg 8 (by decide)
  · exact arg 9 (by decide)
  · exact arg 10 (by decide)

theorem example_pre (same : Bool) : publicContract.pre (exampleState same) := by
  have pw := (examplePowers same).repr
  sig_pre [Sig.bufs.eq_7,Sig.lists.eq_7,Sig.descs.eq_7,Sig.alignedBufs.eq_7,
      publicContract,Spec.Gcm.sealContiguousWithPowersContract,Spec.Gcm.sealContiguousAuxSig,
    Spec.Gcm.sealContiguousSig,Spec.Gcm.withPowersParam,Spec.Gcm.sealWithPowersPre,Spec.Gcm.sealPre,
    abi,argRegs,Gather.stackArgs_three,List.cons_append,List.nil_append]
  cases same <;> simp only [exampleState] at *
  all_goals
    simp [Sig.pairFacts,Sig.conj,List.filterMap_cons,and_assoc]
    repeat' apply And.intro
    all_goals first | exact pw | exact Region.disjoint_of_sep (by decide) | decide

theorem public_verified {v : GcmImpl} {g : GhashWithImpl} (facts : BackendFacts v g) :
    VerifiedScrubbed target (select v.calls g.fn) publicContract 0 := by
  have raw := verified facts
  refine ⟨raw.verified.of_implies ⟨fun _ => public_pre,fun _ _ _ => public_post,fun _ _ _ _ => public_pub,
    ⟨_,example_pre true⟩⟩,?_,fun ty _ h => by cases ty <;> cases h⟩
  intro a b τ υ x y pa pb pub out unknown ea eb
  exact raw.noResidue _ _ _ _ _ _ (public_pre pa) (public_pre pb) (public_pub pub) out unknown ea eb

end VG.Proof.AesGcm.AArch64.Contiguous
