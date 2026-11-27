module

-- separate module: Keep the public parameter and memory layout adaptation independent of the scrubbed return proof.

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Framed
public import VerifiedGarbage.Spec.Gcm.Contiguous
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesGcm.Rounds

/-! # Binding the public RISC-V call to the shared contiguous AES-GCM contract -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Spec.Gcm

abbrev contract := sealContiguousBitslicedContract VG.RISCV64.abi 4656

private abbrev C (p : Args) : Region := ⟨p.ctx,256⟩
private abbrev N (p : Args) : Region := ⟨p.iv,p.ivLen.toNat⟩
private abbrev A (p : Args) : Region := ⟨p.aad,p.aadLen.toNat⟩
private abbrev S (p : Args) : Region := ⟨p.src,p.len.toNat⟩
private abbrev D (p : Args) : Region := ⟨p.dst,p.len.toNat⟩
private abbrev T (p : Args) : Region := ⟨p.tag,16⟩
private abbrev K (p : Args) : Region := ⟨p.keys,1248⟩

private structure PublicBuffers (s : State) : Prop where
  rd : let p := callArgs s; s.rd=[C p,N p,A p]++(if p.src=p.dst then [] else [S p])++[K p,⟨stackArgAddr s 0,24⟩]
  wr : let p := callArgs s; s.wr=[D p,T p]
  stack : let p := callArgs s; ∀ r∈[C p,N p,A p,S p,K p,D p,T p],(below s.sp 4656).Disjoint r
  fit : let p := callArgs s; ∀ r∈[C p,N p,A p,S p,K p,D p,T p],r.base.toNat+r.len≤2^64
  dst : let p := callArgs s; (D p).Disjoint (T p) ∧ (C p).Disjoint (D p) ∧ (D p).Disjoint (K p)
  buffers : let p := callArgs s; Alias true p.src p.dst p.len.toNat

private theorem buffers_caller {s : State} (q : PublicBuffers s) (al : s.sp.toNat%16=0) (space : 4656≤s.sp.toNat)
    (ca : (callArgs s).ctx.toNat%8=0) (ba : (callArgs s).keys.toNat%8=0)
    (nr : (callArgs s).rounds=10 ∨ (callArgs s).rounds=12 ∨ (callArgs s).rounds=14)
    (ks : CtxSlicedRepr s.mem (callArgs s).keys (callArgs s).ctx) : Caller s := by
  let p := callArgs s
  have keySub : Region.Sub ⟨p.keys,960⟩ (K p) := Region.sub_prefix (by decide)
  have supports (r : Region) (hr : r∈p.regions) : ∃ r'∈[C p,N p,A p,S p,K p,D p,T p],r.Sub r' :=
    by
      simp only [Args.regions,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨C p,by simp,fun _ h => h⟩
      · exact ⟨N p,by simp,fun _ h => h⟩
      · exact ⟨A p,by simp,fun _ h => h⟩
      · exact ⟨S p,by simp,fun _ h => h⟩
      · exact ⟨K p,by simp,keySub⟩
      · exact ⟨D p,by simp,fun _ h => h⟩
      · exact ⟨T p,by simp,fun _ h => h⟩
  refine ⟨al,space,?_,?_,?_,?_,covers_mem (q.wr ▸ .head _),covers_mem (q.wr ▸ .tail _ (.head _)),
    q.dst.1.symm,q.dst.2.1,(q.dst.2.2.sub_right keySub).symm,q.buffers,ca,ba,nr,keysAt_of_sliced (by omega) ks⟩
  · intro i hi
    refine ⟨_,List.mem_append_left _ (q.rd ▸ List.mem_append_right _ (.tail _ (.head _))),?_⟩
    exact Offset.contains s.sp (Nat.zero_le _) (by omega) (by decide)
  · intro r hr
    have big : Covers [K p] (s.rd++s.wr) := covers_mem (List.mem_append_left _ (q.rd ▸ List.mem_append_right _ (.head _)))
    have source : Covers [S p] (s.rd++s.wr) := by
      by_cases eq : p.src=p.dst
      · change Covers [⟨p.src,p.len.toNat⟩] _;rw [eq];exact covers_left (covers_mem (q.wr ▸ .head _))
      · apply covers_mem;rw [q.rd];apply List.mem_append_left
        change S p∈[C p,N p,A p]++(if p.src=p.dst then [] else [S p])++_
        simp [eq]
    simp only [Args.regions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact covers_mem (List.mem_append_left _ (q.rd ▸ List.mem_append_left _ (List.mem_append_left _ (.head _))))
    · exact covers_mem (List.mem_append_left _ (q.rd ▸ List.mem_append_left _ (List.mem_append_left _ (.tail _ (.head _)))))
    · exact covers_mem (List.mem_append_left _ (q.rd ▸ List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.head _))))))
    · exact source
    · exact covers_prefix big (by decide : 960≤1248)
    · exact covers_left (covers_mem (q.wr ▸ .head _))
    · exact covers_left (covers_mem (q.wr ▸ .tail _ (.head _)))
  · intro r hr
    simp only [Args.regions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact q.fit (C p) (by simp [p])
    · exact q.fit (N p) (by simp [p])
    · exact q.fit (A p) (by simp [p])
    · exact q.fit (S p) (by simp [p])
    · have hk := q.fit (K p) (by simp [p])
      change p.keys.toNat+1248≤2^64 at hk
      change p.keys.toNat+960≤2^64;omega
    · exact q.fit (D p) (by simp [p])
    · exact q.fit (T p) (by simp [p])
  · intro r hr
    obtain ⟨r',mem,sub⟩ := supports r hr
    exact ((q.stack _ mem).sub_right sub).symm

private abbrev preFields (s : State) := PublicBuffers s ∧ s.sp.toNat%16=0 ∧ 4656≤s.sp.toNat ∧
  (s.gpr .a0).toNat%8=0 ∧ (stackArg s 2).toNat%8=0 ∧
  ((s.gpr .a1).toNat=10 ∨ (s.gpr .a1).toNat=12 ∨ (s.gpr .a1).toNat=14) ∧ CtxSlicedRepr s.mem (stackArg s 2) (s.gpr .a0)

private theorem fields_of_pre {s : State} (h : contract.pre s) : preFields s := by
  sig_pre [contract,sealContiguousBitslicedContract,sealContiguousAuxSig,sealContiguousSig,bitslicedParam,sealBitslicedPre,Spec.Gcm.sealPre,
    VG.RISCV64.abi,VG.RISCV64.argRegs,List.getD,List.range,List.range.loop] at h
  by_cases eq : s.gpr .a6=s.gpr .a7
  · simp [eq,Sig.pairFacts,Sig.conj,List.filterMap_cons,List.filterMap_nil,and_assoc] at h
    obtain ⟨al,sp,_,rd,wr,cd,_,_,_,_,_,dt,dk,_,_,_,bc,bn,ba,bd,bt,bk,_,fc,fn,fa,fd,ft,fk,nr,ks,ca,ka⟩ := h
    refine ⟨⟨?_,wr,?_,?_,⟨dt,cd,dk⟩,.inl eq⟩,al,sp,ca,ka,nr,ks⟩
    · simpa only [callArgs,eq,↓reduceIte,List.cons_append,List.nil_append] using rd
    · simp only [List.forall_mem_cons]
      exact ⟨bc,bn,ba,by simpa only [S,callArgs,eq] using bd,bk,bd,bt,List.forall_mem_nil _⟩
    · simp only [List.forall_mem_cons,C,N,A,S,K,D,T]
      refine ⟨?_,fn,fa,by rwa [eq],?_,fd,?_,List.forall_mem_nil _⟩ <;> omega
  · simp [eq,Sig.pairFacts,Sig.conj,List.filterMap_cons,List.filterMap_nil,and_assoc] at h
    obtain ⟨al,sp,_,rd,wr,cd,_,_,_,_,_,sd,_,dt,dk,_,_,_,bc,bn,ba,bs,bd,bt,bk,_,fc,fn,fa,fs,fd,ft,fk,nr,ks,ca,ka⟩ := h
    refine ⟨⟨?_,wr,?_,?_,⟨dt,cd,dk⟩,.inr sd⟩,al,sp,ca,ka,nr,ks⟩
    · simpa only [callArgs,eq,↓reduceIte,List.cons_append,List.nil_append] using rd
    · simp only [List.forall_mem_cons]
      exact ⟨bc,bn,ba,bs,bk,bd,bt,List.forall_mem_nil _⟩
    · simp only [List.forall_mem_cons,C,N,A,S,K,D,T]
      refine ⟨?_,fn,fa,fs,?_,fd,?_,List.forall_mem_nil _⟩ <;> omega

theorem caller_of_pre {s : State} (h : contract.pre s) : Caller s := by
  obtain ⟨p,al,space,ca,ba,nr,keys⟩ := fields_of_pre h
  exact buffers_caller p al space ca ba nr keys

theorem prepared_of_pre {s : State} (h : contract.pre s) : PreparedCaller s := by
  obtain ⟨q,_,_,_,al,_,ks⟩ := fields_of_pre h
  let p := callArgs s
  let T := p.keys+BitVec.ofNat 64 960
  have sub : (⟨T,288⟩ : Region).Sub (K p) := Offset.sub_base p.keys (by decide)
  have read : Covers [K p] (s.rd++s.wr) := covers_mem (List.mem_append_left _ (q.rd ▸ List.mem_append_right _ (.head _)))
  have alt : T.toNat%8=0 := Spill.al8 al (by decide)
  have apart := (q.stack (K p) (by simp [p])).sub_right sub
  refine ⟨TableAt.of_sliced ks alt ?_ (covers_off read (by decide) (by decide)),apart.symm,(q.dst.2.2.sub_right sub).symm⟩
  exact apart.sub_left (VG.RISCV64.below_sub (by decide) (by decide))

theorem args_of_pub {s t : State} (hp : contract.pub s t) : callArgs s=callArgs t := by
  sig_pub [contract,sealContiguousBitslicedContract,sealContiguousAuxSig,sealContiguousSig,bitslicedParam,
    VG.RISCV64.abi,VG.RISCV64.argRegs,List.getD,List.range,List.range.loop] at hp
  obtain ⟨sp,c,r,n,nl,a,al,src,dst,len,tag,bk⟩ := hp
  simp only [callArgs,allocated,allocd,sp,c,r,n,nl,a,al,src,dst,len,tag,bk]

theorem post_of_sealed {s t : State} (z : sealed s t) : contract.post s t := by
  sig_post [contract,sealContiguousBitslicedContract,sealContiguousAuxSig,sealContiguousSig,bitslicedParam,sealContiguousPost,
    VG.RISCV64.abi,VG.RISCV64.argRegs,List.getD,List.range,List.range.loop]
  intro key valid
  obtain ⟨cx,hh,_⟩ := Proof.AesGcm.keyRounds_ctx valid
  change (_,_) = encryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) _ _ _ _ _ at z
  rw [cx,hh,←encrypt_eq] at z
  exact z.symm

end VG.Proof.AesGcm.RISCV64.Contiguous
