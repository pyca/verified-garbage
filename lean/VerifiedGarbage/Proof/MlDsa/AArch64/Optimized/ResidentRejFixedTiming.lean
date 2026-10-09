import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejFour
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Impl.MlDsa.AArch64.Sample

abbrev PointerCT (rs : List Reg) (c : Prog isa) :=
  ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs rs)) c

theorem startFour_ct : PointerCT [.x0,.x1,.x2] (.block (Rej4.init++Four.initCounts)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem startTwo_ct : PointerCT [.x0,.x1,.x2]
    (.block (Rej4.pro++Rej4.zeroStates++Rej4.absorbPair 0++Two.initCounts)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem flagsFour_ct : PointerCT [.x19] (.block Four.flags) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem flagsTwo_ct : PointerCT [.x19] (.block Two.flags) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem epi_ct : PointerCT [.x19] (.block Rej4.epi) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem sixthFour_ct : PointerCT [.x19] (Four.squeezeN step 840 1) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem sixthTwo_ct : PointerCT [.x19] (Two.squeezeN Two.step 840 1) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem firstFour_ct : PointerCT [.x19]
    (.seq (.block (Four.squeezeSetup 0 5))
      (.seq (five .x22 .x24 .x25) (five .x23 .x26 .x27))) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem firstTwo_ct : PointerCT [.x19]
    (.seq (.block (Two.squeezeSetup 0 5)) (five .x22 .x24 .x25)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
