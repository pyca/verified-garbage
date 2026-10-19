module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedule
public import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem kgG768_schedule : certified 72 [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩]=true := by decide +kernel

theorem kgH768_schedule : certified 136 [⟨.x26,0,lay768.ekLen⟩]=true := by decide +kernel

theorem prf768_schedule : certified 136 [⟨.x28,KEM.RB,33⟩]=true := by decide +kernel

theorem enH768_schedule : certified 136 [⟨.x25,0,lay768.ekLen⟩]=true := by decide +kernel

theorem enG768_schedule : certified 72 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]=true := by decide +kernel

theorem deG768_schedule : certified 72 [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩]=true := by decide +kernel

theorem kgG1024_schedule : certified 72 [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩]=true := by decide +kernel

theorem kgH1024_schedule : certified 136 [⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩]=true := by decide +kernel

theorem prf1024_schedule : certified 136 [⟨.x28,KEM.RB,33⟩]=true := by decide +kernel

theorem enH1024_schedule : certified 136 [⟨.x25,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩]=true := by decide +kernel

theorem enG1024_schedule : certified 72 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]=true := by decide +kernel

theorem deG1024_schedule : certified 72 [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩]=true := by decide +kernel

end VG.Proof.MlKem.AArch64.FixedHash
