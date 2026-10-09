import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.Sha3 (bytesAt)

private theorem bytesAt_append (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a+b)=bytesAt m p a++bytesAt m (p+BitVec.ofNat 64 a) b := by
  simp only [bytesAt,List.range_add,List.map_append,List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply,Offset.add_add]

private theorem candidateBytes_one (m : Mem) (p : Addr) :
    candidateBytes m p 1=bytesAt m p 3 := by
  change [m (p+BitVec.ofNat 64 0),m (p+BitVec.ofNat 64 0+1),m (p+BitVec.ofNat 64 0+2)]=
    [m (p+BitVec.ofNat 64 0),m (p+BitVec.ofNat 64 1),m (p+BitVec.ofNat 64 2)]
  rw [show p+BitVec.ofNat 64 0+1=p+BitVec.ofNat 64 1 by bv_omega,
    show p+BitVec.ofNat 64 0+2=p+BitVec.ofNat 64 2 by bv_omega]

/-- The parser's consecutive candidate view is precisely the existing
byte-addressed XOF stream view. -/
theorem candidateBytes_eq_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    candidateBytes m p n=bytesAt m p (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [candidateBytes_append,candidateBytes_one,ih,show 3*(n+1)=3*n+3 by omega,
      bytesAt_append]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
