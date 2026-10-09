import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedCopyBody

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Keep count_loop ptr_add)
open VG.Proof.MlDsa.Pack (Written)
open VG.Proof.MlDsa.AArch64.Optimized.KeygenPack (written_word)

theorem copyMask_ok (p : Params) (s : State)
    (hin : InRegions (s.rd++s.wr) (pa s t4P) 1024)
    (hout : InRegions s.wr (pa s (yP p (p.ℓ-1))) 1024)
    (hsep : (⟨pa s t4P,1024⟩:Region).Disjoint ⟨pa s (yP p (p.ℓ-1)),1024⟩) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.copyMask p) s fun t=>
      bytesAt t.mem (pa s (yP p (p.ℓ-1))) 1024=bytesAt s.mem (pa s t4P) 1024 ∧
      Frame [⟨pa s (yP p (p.ℓ-1)),1024⟩] s.mem t.mem ∧ Keep [.x0,.x1,.x2,.x9] s t := by
  let dst := pa s (yP p (p.ℓ-1))
  let src := pa s t4P
  unfold Impl.MlDsa.AArch64.Sign.Cached.copyMask
  refine WP.seq (WP.mono (copyGlue_ok (dst:=yP p (p.ℓ-1)) (src:=t4P) (n:=128) (by change Reg.x28∈keptRegs;decide) (by decide) s)
    fun a ⟨⟨h0,h1,h2⟩,ka⟩=>?_)
  refine WP.mono (count_loop (cr:=.x2) (n:=128) (by decide) (fun k u=>
    u.gpr .x0=dst+BitVec.ofNat 64 (8*k) ∧ u.gpr .x1=src+BitVec.ofNat 64 (8*k) ∧
    u.gpr .x2=BitVec.ofNat 64 (128-k) ∧ Keep [.x0,.x1,.x2,.x9] s u ∧
    Frame [⟨dst,1024⟩] s.mem u.mem ∧
    (∀j<8*k,u.mem (dst+BitVec.ofNat 64 j)=s.mem (src+BitVec.ofNat 64 j)))
    (fun k hk u ⟨e0,e1,e2,ku,hf,hb⟩=>?_) ?_) fun t ⟨_,_,_,kt,hf,hb⟩=>?_
  · refine WP.mono (copyBody_ok u ?_ ?_) fun t ⟨hm,t0,t1,t2,kt⟩=>?_
    · rw [ku.rd,ku.wr,e1]
      exact inRegions_sub hin (by omega) (by omega)
    · rw [ku.wr,e0]
      exact inRegions_sub hout (by omega) (by omega)
    · have hw : Written u.mem t.mem (dst+BitVec.ofNat 64 (8*k)) 8
          (fun j=>s.mem (src+BitVec.ofNat 64 (8*k+j))) := by
        rw [hm,e0]
        refine (written_word u.mem _ 8 (u.mem.readW (u.gpr .x1) 64)).congr fun j hj=>?_
        rw [e1]
        simp only [Mem.readW,BitVec.setWidth_eq]
        rw [Mem.extractLsb'_read _ _ hj,ptr_add]
        exact hf.bytes (R:=⟨src,1024⟩) (by simpa only [List.mem_singleton,forall_eq] using hsep)
          (by change 1024≤2^64;decide) (by change 8*k+j<1024;omega)
      obtain ⟨hf',hb'⟩ := Written.step hf hb hw (by omega) (by decide : 1024<2^64)
      refine ⟨⟨?_,?_,?_,(ku.trans kt).mono (by simp),hf',?_⟩,?_⟩
      · rw [t0,e0,show (8:BitVec 64)=BitVec.ofNat 64 8 by rfl,ptr_add,Nat.mul_succ]
      · rw [t1,e1,show (8:BitVec 64)=BitVec.ofNat 64 8 by rfl,ptr_add,Nat.mul_succ]
      · rw [t2,e2,ofNat_sub_one hk]
      · simpa only [Nat.mul_succ] using hb'
      · rw [t2,e2,ofNat_sub_one hk,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
        omega
  · exact ⟨by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h0,
      by simpa only [Nat.mul_zero,VG.Proof.MlKem.AArch64.ptr_zero] using h1,
      h2,ka.keep.mono (by simp),by rw [ka.mem];exact Frame.refl _ _,by intro j hj;omega⟩
  · refine ⟨?_,hf,kt⟩
    simp only [bytesAt]
    exact List.map_congr_left fun i hi=>hb i (List.mem_range.mp hi)

end VG.Proof.MlDsa.AArch64.Sign.Cached
