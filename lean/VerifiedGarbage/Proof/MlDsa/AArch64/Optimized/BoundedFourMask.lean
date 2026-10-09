import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourAccept
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def maskCode : List Instr :=
 [.umov .x .x6 .v2 0,.umov .x .x7 .v2 1,.add .x .x6 .x6 .x7,
  .lsr .x .x7 .x6 32,.add .x .x6 .x6 .x7,.logic .and .x .x6 .x6 .x11]

theorem exec_umov_double (s : State) (d : Reg) (n : VReg) {i : Nat} (hi : i<2) :
    exec (.umov .x d n i) s=some (s.write .x d ((s.v n).extractLsb' (i*64) 64)) := by
  simp only [exec,Size.bits,show i*64<128 by omega,ite_true,Nat.mul_comm]

theorem maskCode_ok (s : State) (h15 : s.gpr .x11=15) :
    WP isa (.block maskCode) s fun t =>
      ((t.gpr .x6=maskReduce (s.v .v2) ∧ t.mem=s.mem) ∧ Keep [.x6,.x7] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold maskCode maskReduce
  arun [exec_umov_double (i := 0) (hi := by decide),
    exec_umov_double (i := 1) (hi := by decide),h15]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
