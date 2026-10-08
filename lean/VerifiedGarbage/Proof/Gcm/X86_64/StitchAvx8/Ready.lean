import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Templates

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

/-- The state after setup and before the first AES or hash batch. -/
structure Ready (s₀ : State) (P : Nat → Block) (s : State) : Prop where
  env : Env s₀ P s
  templates : Templates s₀ 0 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + 8
  cursor : s.gpr .rdx = dp s₀
  remaining : s.gpr .r9 = s₀.gpr .r9
  hash : s.lane .xmm2 0 = y₀ s₀
  frame : Frame [pR s₀] s₀.mem s.mem

end VG.Proof.Gcm.X86_64.StitchAvx8
