import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowInputFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def lowPairAccept (g : Nat) (v : Values) (out : Addr) (c : LowConstants) (m : Mem)
    (e : Nat) (i : LowIndex) : Prop :=
  lowMask g m (out+BitVec.ofNat 64 (lowOff i)) (lowValue0 v i) c e=0 ∧
  lowMask g m (out+BitVec.ofNat 64 (lowOff i+128)) (lowValue1 v i) c e=0

/-- A paired r0 sequence accepts precisely all its original-input norm checks. -/
theorem lowRun_flag_zero_iff (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (hn : is.Nodup)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) {e : Nat} (he : e<4) :
    vword (lowRun g v out aux c d is).flags e=0 ↔
      vword d.flags e=0 ∧ ∀i∈is,lowPairAccept g v out c d.mem e i := by
  induction is generalizing d with
  | nil => simp only [lowRun,List.not_mem_nil,false_implies,implies_true,and_true]
  | cons i is ih =>
    have hn' := List.nodup_cons.mp hn
    rw [lowRun,ih _ hn'.2,lowPair_flag_zero _ _ _ _ _ _ _ _ _ he]
    have ht : (∀j∈is,lowPairAccept g v out c
        (lowPairStep g (lowValue0 v i) (lowValue1 v i)
          (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
          (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem e j) ↔
        ∀j∈is,lowPairAccept g v out c d.mem e j := by
      have hp (j : LowIndex) (hj : j∈is) : lowPairAccept g v out c
          (lowPairStep g (lowValue0 v i) (lowValue1 v i)
            (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
            (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem e j ↔
          lowPairAccept g v out c d.mem e j := by
        have hnij : j≠i := by intro h; subst j; exact hn'.1 hj
        have h0 := lowPair_other_input g v out aux c d hnij 0 hd
        have h1 := lowPair_other_input g v out aux c d hnij 1 hd
        simp only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at h0 h1
        unfold lowPairAccept
        rw [lowMask_read_eq _ _ _ _ _ h0,lowMask_read_eq _ _ _ _ _ h1]
      exact ⟨fun h j hj => (hp j hj).mp (h j hj),fun h j hj => (hp j hj).mpr (h j hj)⟩
    rw [ht]
    simp only [List.mem_cons,forall_eq_or_imp,lowPairAccept,and_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
