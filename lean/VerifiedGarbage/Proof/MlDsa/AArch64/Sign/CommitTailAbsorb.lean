import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailWord
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords xorWords_get)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

/-- One word extends the commitment prefix without touching the paired mask. -/
theorem lowWord_step {s : State} {A B : Spec.Sha3.State} {m : Mem} {p : Addr} {j : Nat}
    (hj : j<17) (hm : s.mem=m) (h5 : s.gpr .x5=p)
    (hp : Pairs s (xorWords A m p j) B)
    (hin : InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block (lowWord (vreg j) (8*j))) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=m ∧ Pairs t (xorWords A m p (j+1)) B := by
  have h25 : vreg j≠.v25 := by
    change vreg j≠vreg 25
    rw [ne_eq,vreg_inj j (by omega) 25 (by decide)]
    omega
  refine WP.mono (lowWord_ok h25 ⟨by omega,by omega⟩ (by rw [h5]; exact hin))
    fun t ⟨hk,hmt,hv,ht⟩ => ⟨hk,hmt.trans hm,?_⟩
  intro i hi
  by_cases he : i=j
  · subst i
    rw [ht,hp j (by omega),hm,h5,pair_xor]
    simp only [getElem!_pos (xorWords A m p j) j (by omega),
      getElem!_pos (xorWords A m p (j+1)) j (by omega), getElem!_pos B j (by omega)]
    rw [xorWords_get _ _ _ _ _ (by omega),xorWords_get _ _ _ _ _ (by omega)]
    simp only [Nat.lt_irrefl,ite_false,show j<j+1 by omega,ite_true]
    rw [show A[j] ^^^ (0:BitVec 64)=A[j] from BitVec.xor_zero,
      show B[j] ^^^ (0:BitVec 64)=B[j] from BitVec.xor_zero]
  · have hij : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega) j (by omega)]; exact he
    have hi25 : vreg i≠.v25 := by
      change vreg i≠vreg 25
      rw [ne_eq,vreg_inj i (by omega) 25 (by decide)]
      omega
    rw [hv _ hij hi25,hp i hi]
    have hh : (xorWords A m p j)[i]! = (xorWords A m p (j+1))[i]! := by
      simp only [getElem!_pos (xorWords A m p j) i hi,
        getElem!_pos (xorWords A m p (j+1)) i hi]
      rw [xorWords_get _ _ _ _ _ hi,xorWords_get _ _ _ _ _ hi]
      have hc : (i<j)=(i<j+1) := propext (by omega)
      simp only [hc]
    rw [hh]

/-- Fixed-count low-lane absorption leaves every high lane unchanged. -/
theorem lowWords_ok {s : State} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) (n : Nat) (hn : n≤17)
    (hin : ∀j<n, InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block ((List.range n).flatMap fun j => lowWord (vreg j) (8*j))) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      Pairs t (xorWords A s.mem (s.gpr .x5) n) B := by
  let I := fun j t => RegKeep [.x7] s t ∧ t.mem=s.mem ∧
    Pairs t (xorWords A s.mem (s.gpr .x5) j) B
  have hzero : xorWords A s.mem (s.gpr .x5) 0=A := by
    apply Vector.ext
    intro i hi
    simp only [xorWords_get, Nat.not_lt_zero, ite_false]
    exact BitVec.xor_zero
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht => ?_) n (Nat.le_refl _) s ?_
  · rcases ht with ⟨hk,hm,hp⟩
    refine WP.mono (lowWord_step (by omega) hm (hk.gpr .x5 (by decide)) hp ?_)
      fun u ⟨hk',hm',hp'⟩ => ⟨(hk.trans hk').mono (by simp),hm',hp'⟩
    rw [hk.rd,hk.wr]
    exact hin j hj
  · exact ⟨RegKeep.refl _ _,rfl,by rw [hzero]; exact hp⟩

/-- A complete SHAKE-rate block advances only the commitment input pointer. -/
theorem full_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<17, InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block full) s fun t =>
      RegKeep [.x5,.x7] s t ∧ t.mem=s.mem ∧
      t.gpr .x5=s.gpr .x5+136 ∧
      Pairs t (xorWords A s.mem (s.gpr .x5) 17) B := by
  rw [full,WP.block_append_iff]
  refine WP.mono (lowWords_ok hp 17 (by decide) hin) fun t ⟨hk,hm,hp'⟩ => ?_
  refine VG.Proof.Sha3.AArch64.WP.cons rfl (WP.block_nil_iff.mpr ?_)
  refine ⟨?_,hm,?_,hp'⟩
  · refine ⟨fun r hr => ?_,hk.rd,hk.wr,hk.sp⟩
    have h5 : r≠.x5 := by intro he; apply hr; simp only [he,List.mem_cons,true_or]
    simp only [RegUpd.gpr_write,h5,ite_false]
    exact hk.gpr r (by simp only [List.mem_cons,not_or] at hr ⊢; exact hr.2)
  · simp only [RegUpd.gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq]
    rw [hk.gpr .x5 (by decide)]
    rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
