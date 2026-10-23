module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.InitAese

/-!
# AES-GCM's key setup on AArch64, for each implementation

`vg_aes_gcm_init` for the implementations `v`: the leaf of
`Impl/AesGcm/AArch64/InitAese.lean` for those with `aeseInit`, which uses no
stack, and otherwise the calls of `v`'s key expansion and counter mode, with
their working space on the stack (`init_framed`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64

/-- `vg_aes_gcm_init`'s code for `v`. -/
def initCode (v : GcmImpl) : Prog isa :=
  if v.aeseInit then Impl.AesGcm.AArch64.InitAese.init
  else Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (Impl.AesGcm.AArch64.init v.callees)

/-- The stack `initCode v` uses. -/
def initStack (v : GcmImpl) : Nat := if v.aeseInit then 0 else 2560

theorem initCode_verified (v : GcmImpl) :
    Verified AArch64.target (initCode v) (Spec.Gcm.initContract AArch64.abi (initStack v)) := by
  unfold initCode initStack
  cases v.aeseInit
  · exact init_framed v
  · exact InitAese.init_verified

end VG.Proof.AesGcm.AArch64
