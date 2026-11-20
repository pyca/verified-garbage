module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyInitVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInitVerified
public import VerifiedGarbage.Impl.Ffdh.Arm.Fn

/-!
# FFDH's functions on ARMv7, without secret residue

Each function as emitted (`Impl.Ffdh.Arm.Fn`) returns with the registers a
callee may change set to constants, and the stack its contract reserves
zeroed if it has frames; `Fn` below has the theorem of each, which its
registration binds.

The initializations have no frames (`Arm.Scrub.verifiedScrubbed`). What the
cleanup of the others needs of their code (`Arm.Scrub.scrubSideF`) is
`CodeOk` of it, which each implementation states of its own code
(`Backend.checkDomain_ok`, by `lit_decide` where it is defined), and their
postconditions read the memory on return only within their buffers
(`Arm.Scrub.PostOut`): those below do not read it at all.
-/

@[expose] public section

namespace VG.Proof.Ffdh.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub

theorem checkDomainOut :
    PostOut (Spec.Ffdh.checkDomainContract (abi.withConsts Impl.Ffdh.Arm.VettedGroups.tableConsts) 128)
      (Spec.Ffdh.checkDomainSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen _ h => by
    iterate 5
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact h

theorem checkPrivateOut :
    PostOut (Spec.Ffdh.checkPrivateContract abi 128) (Spec.Ffdh.checkPrivateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    iterate 9
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact h

theorem frameOk_128 : FrameOk 128 := by decide

end VG.Proof.Ffdh.Arm.Scrub

namespace VG.Proof.Ffdh.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ffdh_key_generation_init`. -/
theorem keyInit : VerifiedScrubbed target Impl.Ffdh.Arm.Fn.keyInit (Spec.Ffdh.keyInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.Ffdh.keyInitApi)
    { code := Impl.Ffdh.Arm.KeyGeneration.init, verified := Proof.Ffdh.Arm.keyInit_verified } rfl

/-- `vg_ffdh_parameter_generation_init`. -/
theorem parameterInit :
    VerifiedScrubbed target Impl.Ffdh.Arm.Fn.parameterInit (Spec.Ffdh.parameterInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.Ffdh.parameterInitApi)
    { code := Impl.Ffdh.Arm.Generation.init, verified := Proof.Ffdh.Arm.parameterInit_verified } rfl

/-- `vg_ffdh_check_domain`, with the implementation `v`. -/
theorem checkDomain (v : Backend) :
    VerifiedScrubbed target (Impl.Ffdh.Arm.Fn.checkDomain v.checkDomain)
      (Spec.Ffdh.checkDomainContract (abi.withConsts Impl.Ffdh.Arm.VettedGroups.tableConsts) 128) 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.checkDomainApi)
    { code := v.checkDomain, verified := v.checkDomain_verified }
    Scrub.checkDomainOut (scrubSideF_of v.checkDomain_ok Scrub.frameOk_128 _)

/-- `vg_ffdh_check_private`, with the implementation `v`. -/
theorem checkPrivate (v : Backend) :
    VerifiedScrubbed target (Impl.Ffdh.Arm.Fn.checkPrivate v.checkPrivate)
      (Spec.Ffdh.checkPrivateContract abi 128) 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.checkPrivateApi)
    { code := v.checkPrivate, verified := v.checkPrivate_verified }
    Scrub.checkPrivateOut (scrubSideF_of v.checkPrivate_ok Scrub.frameOk_128 _)

end VG.Proof.Ffdh.Arm.Fn
