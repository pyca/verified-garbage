import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Sample (movQ rbBound)

def scalarSetup (η : Nat) : List Instr :=
 [.movz .x .x6 256 0,.sub .x .x6 .x6 .x4,.lsl .x .x6 .x6 2,.add .x .x3 .x3 .x6,
 .movz .x .x5 272 0]++movQ .x9++
 [.movz .x .x10 (BitVec.ofNat 16 η) 0,.movz .x .x11 15 0,
  .movz .x .x15 (BitVec.ofNat 16 (rbBound η)) 0]

private theorem count_shift : ∀j≤256,
    ((256#64-BitVec.ofNat 64 (256-j))<<<2)=BitVec.ofNat 64 (4*j) := by
  intro j hj
  have hs:=BitVec.ofNat_sub_ofNat_of_le (w := 64) 256 (256-j) (by omega) (by omega)
  rw [hs,show 256-(256-j)=j by omega,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 j * BitVec.ofNat 64 4=BitVec.ofNat 64 (4*j)
  rw [←BitVec.ofNat_mul,Nat.mul_comm]

structure ScalarReady (η : Nat) (p : Addr) (j : Nat) (s : State) : Prop where
 output : s.gpr .x3=VG.Proof.MlDsa.Sample.coeffAddr p j
 bytes : s.gpr .x5=272
 q : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q
 eta : s.gpr .x10=BitVec.ofNat 64 η
 mask : s.gpr .x11=15
 bound : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)

theorem scalarSetup_ok {s : State} {η j : Nat} (he : η=2∨η=4) (hj : j≤256)
    {p : Addr} (h3 : s.gpr .x3=p) (h4 : s.gpr .x4=BitVec.ofNat 64 (256-j)) :
    WP isa (.block (scalarSetup η)) s fun t=>
      InitKeep [.x3,.x5,.x6,.x9,.x10,.x11,.x15] [] s t ∧ ScalarReady η p j t := by
  have hh : WP isa (.block (scalarSetup η)) s fun t=>
      (ScalarReady η p j t ∧ t.mem=s.mem) ∧ Keep [.x3,.x5,.x6,.x9,.x10,.x11,.x15] s t := by
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
    rcases he with rfl|rfl <;>
      unfold scalarSetup movQ <;>
      arun [h3,h4,count_shift j hj,VG.Proof.MlDsa.Sample.coeffAddr]
    all_goals constructor <;> simp [State.write,Size.bits,VG.Proof.MlDsa.Sample.coeffAddr,
      count_shift j hj,Spec.MlDsa.q,VG.Proof.MlDsa.Sample.rbB,rbBound]
  refine WP.mono (WP.keepV (by rfl) hh) fun t ⟨⟨⟨hc,hm⟩,hk⟩,hv⟩=>
    ⟨⟨hk,hm,fun _ _=>congrFun hv _⟩,hc⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
