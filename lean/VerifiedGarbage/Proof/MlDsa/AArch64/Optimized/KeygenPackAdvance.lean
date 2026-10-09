import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackGroup

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def advance (d c : Nat) : List Instr :=
  [.addImm .x .x0 .x0 (4*c),.addImm .x .x2 .x2 (d*c/8),.subImm .x .x15 .x15 1]

theorem advance_ok (d c : Nat) (hd : d≤20) (hc : c≤8) (s : State) :
    WP isa (.block (advance d c)) s fun t =>
      ((t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (4*c) ∧
        t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (d*c/8) ∧
        t.gpr .x15=s.gpr .x15-1 ∧ t.mem=s.mem) ∧ Keep [.x0,.x2,.x15] s t) ∧ t.v=s.v := by
  have hh := Nat.mul_le_mul hd hc
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold advance
  have h4 : 4*c<4096 := by omega
  have h8 : d*c/8<4096 := by omega
  arun [exec,h4,h8]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
