import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideStep

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (acc acc_length)
open VG.Spec.MlDsa (Zq q)

/-- Consecutive complete three-byte candidates in the sampler buffer. -/
def candidateBytes (m : Mem) (p : Addr) (n : Nat) : List Byte :=
 (List.range n).flatMap fun j =>
   [m (p+BitVec.ofNat 64 (3*j)),m (p+BitVec.ofNat 64 (3*j)+1),
    m (p+BitVec.ofNat 64 (3*j)+2)]

theorem candidateFold_succ (m : Mem) (p : Addr) (n : Nat) (L : List Zq) :
    candidateFold m p (n+1) L=
      acc (candidateFold m p n L) (candidate m (p+BitVec.ofNat 64 (3*n))) := by
  simp only [candidateFold,List.range_succ,List.map_append,List.map_cons,List.map_nil,
    List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem candidateFold_length (m : Mem) (p : Addr) (n : Nat) (L : List Zq) :
    L.length≤(candidateFold m p n L).length ∧
      (candidateFold m p n L).length≤L.length+n := by
  induction n with
  | zero => exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  | succ n ih =>
    rw [candidateFold_succ,acc_length]
    split <;> omega

theorem candidateBytes_length (m : Mem) (p : Addr) (n : Nat) :
    (candidateBytes m p n).length=3*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [candidateBytes,List.range_succ,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.length_append,List.length_cons,List.length_nil]
    change (candidateBytes m p n).length+3=3*(n+1)
    rw [ih]
    omega

/-- A vector-sized batch with enough output capacity is exactly the shared
rejection-sampling fold, including every possible rejection pattern. -/
theorem candidateFold_eq_rnFold (m : Mem) (p : Addr) (n : Nat) (L : List Zq)
    (h : L.length+n≤256) :
    candidateFold m p n L=rnFold L (candidateBytes m p n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hb := (candidateFold_length m p n L).2
    have hi := ih (by omega)
    rw [candidateFold_succ]
    unfold candidateBytes
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    change acc (candidateFold m p n L) (candidate m (p+BitVec.ofNat 64 (3*n)))=
      rnFold L (candidateBytes m p n ++ _)
    rw [rnFold_snoc L (by rw [candidateBytes_length]; omega),←hi,
      rnStep,ite_eq_left (by change (candidateFold m p n L).length<256; omega)]
    rfl

/-- Splitting a candidate stream does not change the byte order. -/
theorem candidateBytes_append (m : Mem) (p : Addr) (a b : Nat) :
    candidateBytes m p (a+b)=candidateBytes m p a ++
      candidateBytes m (p+BitVec.ofNat 64 (3*a)) b := by
  simp only [candidateBytes,List.range_add,List.flatMap_append,List.flatMap_map]
  congr 1
  congr 1
  funext j
  simp only [Nat.mul_add,Offset.add_add]

/-- A batch continues the global shared fold from its current accepted
prefix, with no extra normalization or skipped rejected inputs. -/
theorem candidateFold_continue (m : Mem) (p : Addr) (a b : Nat) (L : List Zq)
    (h : (rnFold L (candidateBytes m p a)).length+b≤256) :
    candidateFold m (p+BitVec.ofNat 64 (3*a)) b (rnFold L (candidateBytes m p a))=
      rnFold L (candidateBytes m p (a+b)) := by
  rw [candidateFold_eq_rnFold _ _ _ _ h,candidateBytes_append,
    rnFold_append _ _ _ (by rw [candidateBytes_length]; omega)]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
