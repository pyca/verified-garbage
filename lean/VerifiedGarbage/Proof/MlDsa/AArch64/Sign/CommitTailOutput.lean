import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailPadding

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (RatePairs)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

private theorem zip1_low (a b : BitVec 128) :
    VPermOp.eval .zip1 .d2 a b=ofVDwords (vdword a 0) (vdword b 0) :=
by
  simp only [VPermOp.eval,VArr.lanes,VArr.ofLanes,List.length_cons,List.length_nil,
    Nat.reduceAdd,Nat.reduceDiv]
  simp only [List.range_succ,List.range_zero,List.nil_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.getD_cons_zero,List.getD_cons_succ]
  congr 1 <;> rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]

private theorem pair_ok {s : State} {A B : Spec.Sha3.State} {p : Addr} {i : Nat}
    (hi : 2*i+1<25) (hp : Pairs s A B) (hptr : s.gpr .x2=p)
    (hout : InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block [.vop (.perm .zip1 .d2 .v25 (vreg (2*i)) (vreg (2*i+1))),
      .strq .v25 .x2 (16*i)]) s fun t => RegKeep [] s t ∧ Pairs t A B ∧
      t.mem=s.mem.write (p+BitVec.ofNat 64 (16*i)) 16 (ofVDwords A[2*i]! A[2*i+1]!) := by
  refine wp_vop (d:=.v25) rfl fun a ha =>
    wp_strq ⟨by omega,by omega⟩ (by rw [ha.gpr,hptr]) (by rw [ha.wr]; exact hout)
      fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((RegKeep.vupd ha).trans (RegKeep.vmem ht)).mono (by simp),?_,?_⟩
  · intro j hj
    have hj25 : vreg j≠.v25 := by
      change vreg j≠vreg 25
      rw [ne_eq,vreg_inj j (by omega) 25 (by decide)]; omega
    rw [ht.v,ha.get _ hj25]
    exact hp j hj
  · rw [ht.mem,ha.v,ha.mem,zip1_low,hp _ (by omega),hp _ hi,
      vdword_ofVDwords_0,vdword_ofVDwords_0]

/-- The first-lane digest is copied directly to its caller output. -/
theorem output_ok {s : State} {A B : Spec.Sha3.State} {p : Addr} (n : Nat)
    (hn : n≤12) (hp : Pairs s A B) (hptr : s.gpr .x2=p)
    (hout : ∀i<n, InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (output (16*n))) s fun t =>
      RegKeep [] s t ∧ Pairs t A B ∧ RatePairs t.mem p n A ∧ Frame [⟨p,16*n⟩] s.mem t.mem := by
  unfold output
  rw [show 16*n/16=n by omega]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ Pairs t A B ∧ RatePairs t.mem p k A ∧ Frame [⟨p,16*n⟩] s.mem t.mem)
    (fun k t hk ht => ?_) n (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,hp,fun _ h => by omega,Frame.refl _ _⟩
  refine WP.mono (pair_ok (by omega) ht.2.1 ((ht.1.gpr .x2 (by simp)).trans hptr)
    (by rw [ht.1.wr]; exact hout k hk)) fun u hu => ?_
  refine ⟨(ht.1.trans hu.1).mono (by simp),hu.2.1,?_,?_⟩
  · intro i hi
    rw [hu.2.2]
    by_cases he : i=k
    · subst i; exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep p (d:=16*i) (n:=16) (e:=16*k) (k:=16)
        (by omega) (by omega) (by omega)) (by decide)]
      exact ht.2.2.1 i (by omega)
  · rw [hu.2.2]
    exact ht.2.2.2.write (r:=⟨p,16*n⟩) (by simp) _
      (Offset.contains_base p (by omega) (by omega))

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
