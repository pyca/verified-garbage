import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MatrixMaskBody

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (maskRun)

theorem maskRun_add (m : Mem) (p : Addr) (v : BitVec 128) (n k : Nat) :
    maskRun (maskRun m p v n) (p+BitVec.ofNat 64 (16*n)) v k=maskRun m p v (n+k) := by
  induction k with
  | zero => simp only [maskRun,Nat.add_zero]
  | succ k ih =>
    rw [maskRun,ih,show n+(k+1)=(n+k)+1 by omega,maskRun]
    simp only [Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

structure LoopInv (σ s : State) (p : Addr) (v : BitVec 128) (N j : Nat) : Prop where
  bound : j≤N
  keep : Keep [.x1,.x2] σ s
  vec : ∀r,r≠.v1→s.v r=σ.v r
  mem : s.mem=maskRun σ.mem p v (4*j)
  ptr : s.gpr .x1=p+BitVec.ofNat 64 (64*j)
  count : s.gpr .x2=BitVec.ofNat 64 (N-j)
  mask : s.v .v0=v

theorem step_ok {σ s : State} {p : Addr} {v : BitVec 128} {N j : Nat}
    (hi : LoopInv σ s p v N j) (hj : j<N) (_hN : N≤64)
    (hr : ∀i<4*N,InRegions (σ.rd++σ.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4*N,InRegions σ.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block body) s (fun t => LoopInv σ t p v N (j+1)) := by
  have addr k : s.gpr .x1+BitVec.ofNat 64 (16*k)=p+BitVec.ofNat 64 (16*(4*j+k)) := by
    rw [hi.ptr,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show 64*j+16*k=16*(4*j+k) by omega]
  refine WP.mono (body_ok (fun k hk => by rw [hi.keep.rd,hi.keep.wr,addr]; exact hr _ (by omega))
    (fun k hk => by rw [hi.keep.wr,addr]; exact hw _ (by omega))) fun t ⟨ht,hv,hm,hp,hc⟩ => ?_
  refine ⟨by omega,(hi.keep.trans ht).mono (by decide),fun r hn => (hv r hn).trans (hi.vec r hn),?_,?_,?_,?_⟩
  · rw [hm,hi.mem,hi.mask,hi.ptr,show 64*j=16*(4*j) by omega,maskRun_add]
    congr 1
  · rw [hp,hi.ptr,BitVec.add_assoc]
    change p+(BitVec.ofNat 64 (64*j)+BitVec.ofNat 64 64)=_
    rw [←BitVec.ofNat_add]
    congr 1
  · rw [hc,hi.count]
    change BitVec.ofNat 64 (N-j)-BitVec.ofNat 64 1=_
    rw [BitVec.ofNat_sub_ofNat_of_le (N-j) 1 (by decide) (by omega)]
    congr 1
  · rw [hv .v0 (by decide),hi.mask]

theorem loop_ok {σ s : State} {p : Addr} {v : BitVec 128} {N j : Nat}
    (hi : LoopInv σ s p v N j) (hj : j<N) (hN : N≤64)
    (hr : ∀i<4*N,InRegions (σ.rd++σ.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4*N,InRegions σ.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.loop (.block body) (.nonzero .x .x2)) s (fun t => LoopInv σ t p v N N) := by
  refine WP.loop (M := isa) (fun rank s => ∃j,rank=N-j ∧ LoopInv σ s p v N j ∧ j<N)
    ?_ (N-j) s ⟨j,rfl,hi,hj⟩
  rintro rank s ⟨j,rfl,hi,hj⟩
  refine WP.mono (step_ok hi hj hN hr hw) fun t ht => ?_
  have hg : isa.eval (.nonzero .x .x2) t=some (decide (j+1<N)) := by
    rw [eval_nonzero,ht.count,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    congr 1
    apply decide_eq_decide.mpr
    have := ht.bound
    omega
  by_cases hn : j+1<N
  · exact .inr ⟨by rw [hg,decide_eq_true hn],N-(j+1),by omega,j+1,rfl,ht,hn⟩
  · have he : j+1=N := by omega
    exact .inl ⟨by rw [hg,decide_eq_false hn],by simpa only [he] using ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
