import VerifiedGarbage.Proof.Divstep.HullData

/-!
# The hulls of the divstep bound: the inclusions

Each of the ten inclusions between the hulls, checked by the kernel
(`Incl.ok`, sound by `Incl.ok_sound`).
-/

namespace VG.Proof.Divstep

theorem inclInit_ok : inclInit.ok = true := by decide +kernel
theorem inclOuter_ok : inclOuter.ok = true := by decide +kernel
theorem incl0_ok : incl0.ok = true := by decide +kernel
theorem incl1_ok : incl1.ok = true := by decide +kernel
theorem incl3_ok : incl3.ok = true := by decide +kernel
theorem incl5_ok : incl5.ok = true := by decide +kernel
theorem inclN2_ok : inclN2.ok = true := by decide +kernel
theorem inclN1_ok : inclN1.ok = true := by decide +kernel
theorem inclN4scale_ok : inclN4scale.ok = true := by decide +kernel
theorem inclN3scale_ok : inclN3scale.ok = true := by decide +kernel

end VG.Proof.Divstep
