import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejGuard
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def advanceCore : List Instr :=
 [.lsl .x .x7 .x6 2,.add .x .x3 .x3 .x7,.sub .x .x4 .x4 .x6,
  .addImm .x .x2 .x2 2,.subImm .x .x5 .x5 2]

private theorem countShift : ∀c≤4,(BitVec.ofNat 64 c<<<2)=BitVec.ofNat 64 (4*c) := by decide

theorem advanceCore_ok {s : State} {c r n : Nat} (hc : c≤4) (hr : c≤r) (hn : 2≤n)
    (h6 : s.gpr .x6=BitVec.ofNat 64 c)
    (h4 : s.gpr .x4=BitVec.ofNat 64 r) (h5 : s.gpr .x5=BitVec.ofNat 64 n) :
    WP isa (.block advanceCore) s fun t=>
      ((t.gpr .x2=s.gpr .x2+2 ∧ t.gpr .x3=s.gpr .x3+BitVec.ofNat 64 (4*c) ∧
        t.gpr .x4=BitVec.ofNat 64 (r-c) ∧ t.gpr .x5=BitVec.ofNat 64 (n-2) ∧ t.mem=s.mem) ∧
        Keep [.x2,.x3,.x4,.x5,.x7] s t) ∧ t.v=s.v := by
  apply WP.keepV (by decide)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold advanceCore
  arun [h6,h4,h5,countShift c hc]
  exact ⟨rfl,BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) hr,
    BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by decide) hn⟩

theorem guard_ok {s : State} (h16 : s.gpr .x16=4) (h0 : s.gpr .x0=0) :
    WP isa (.block [.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs]) s fun t=>
      Only [.x8] s t ∧ t.v=s.v ∧
      t.gpr .x8=if 4≤(s.gpr .x4).toNat then s.gpr .x5 else 0 := by
  refine WP.mono (ResidentRej.compareChooseReg_ok .x8 .x4 .x16 .x5 .x0
    (by decide) (by decide)) fun t ⟨hk,hv,hx⟩=>⟨hk,hv,?_⟩
  rw [h16,h0] at hx
  exact hx

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
