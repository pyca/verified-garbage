import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourStream
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def squeezeArgs (off : Nat) : List Instr :=
 [Impl.MlKem.AArch64.mov .x22 .x19,.addImm .x .x23 .x19 400,
 .addImm .x .x24 .x19 (840+off),.addImm .x .x25 .x19 (1384+off),
 .addImm .x .x26 .x19 (1928+off),.addImm .x .x27 .x19 (2472+off),.movz .x .x28 2 0]

theorem squeezeArgs_ok (s : State) {off : Nat} (ho : off≤272) :
    WP isa (.block (squeezeArgs off)) s fun t=>
      ((t.gpr .x22=s.gpr .x19 ∧ t.gpr .x23=s.gpr .x19+400 ∧
        t.gpr .x24=s.gpr .x19+BitVec.ofNat 64 (840+off) ∧
        t.gpr .x25=s.gpr .x19+BitVec.ofNat 64 (1384+off) ∧
        t.gpr .x26=s.gpr .x19+BitVec.ofNat 64 (1928+off) ∧
        t.gpr .x27=s.gpr .x19+BitVec.ofNat 64 (2472+off) ∧ t.gpr .x28=2 ∧t.mem=s.mem) ∧
        Keep [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold squeezeArgs Impl.MlKem.AArch64.mov
  have h0 : 840+off<4096 := by omega
  have h1 : 1384+off<4096 := by omega
  have h2 : 1928+off<4096 := by omega
  have h3 : 2472+off<4096 := by omega
  arun [h0,h1,h2,h3]
  rfl

def squeezeAdvance : List Instr :=
 [.addImm .x .x24 .x24 136,.addImm .x .x25 .x25 136,
 .addImm .x .x26 .x26 136,.addImm .x .x27 .x27 136,.subImm .x .x28 .x28 1]

theorem squeezeAdvance_ok (s : State) :
    WP isa (.block squeezeAdvance) s fun t=>
      ((t.gpr .x24=s.gpr .x24+136 ∧ t.gpr .x25=s.gpr .x25+136 ∧
        t.gpr .x26=s.gpr .x26+136 ∧ t.gpr .x27=s.gpr .x27+136 ∧
        t.gpr .x28=s.gpr .x28-1 ∧t.mem=s.mem) ∧
        Keep [.x24,.x25,.x26,.x27,.x28] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold squeezeAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
