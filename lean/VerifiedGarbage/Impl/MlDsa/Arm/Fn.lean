module

public import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.Inst
public import VerifiedGarbage.Impl.MlDsa.Arm.PkTr
public import VerifiedGarbage.Impl.MlDsa.Arm.PreparedKey
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Impl.MlDsa.Arm.Message
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# ML-DSA's functions on ARMv7, as emitted

Each public function of the parameter set `p` is its code, with this
library's primitives, then its cleanup (`Impl.Scrub.Arm.scrubAll`): the
stack its contract reserves zeroed, and the registers a callee may change
set to constants, but the 32 bits of its result (`pk_tr` and the
preparations of keys return none). The wipe is a frame of the
model, of a multiple of 8 bytes:

* `pk_tr`: 8 bytes, which its sponge uses.
* Key generation: 40, and the preparations of keys: 48.
* `sign` and `sign_prepared`: 48, and `verify` and `verify_prepared`: 56.
* The message functions: 56.

The message functions call the functions on `μ` (`vg_<module>_sign`, …) as
they are verified, without the wipe, under names of their own
(`signEntryName`, …), which the emitter writes as internal functions: their
own wipe covers the frames of those calls.
-/

@[expose] public section

namespace VG.Impl.MlDsa.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm
open VG.Spec.MlDsa (Params)

/-- The names the message functions call `vg_<module>_sign`,
`vg_<module>_sign_prepared`, `vg_<module>_verify` and
`vg_<module>_verify_prepared` by, as they are verified, without the wipe. -/
def signEntryName (module : String) : String := s!"vg_{module}_sign_entry"
def signPreparedEntryName (module : String) : String := s!"vg_{module}_sign_prepared_entry"
def verifyEntryName (module : String) : String := s!"vg_{module}_verify_entry"
def verifyPreparedEntryName (module : String) : String := s!"vg_{module}_verify_prepared_entry"

/-- `vg_<module>_keygen`. -/
def keyGen (p : Params) : Prog isa := scrubAll 32 40 (KeyGen.keyGen KeyGen.prims p)

/-- `vg_<module>_pk_tr`. -/
def pkTr (p : Params) : Prog isa := scrubAll 0 8 (PkTr.pkTr p)

/-- `vg_<module>_prepare_verifying_key`. -/
def preparePublic (p : Params) : Prog isa := scrubAll 0 48 (PreparedKey.preparePublic Sign.prims p)

/-- `vg_<module>_prepare_signing_key`. -/
def prepareSecret (p : Params) : Prog isa := scrubAll 0 48 (PreparedKey.prepareSecret Sign.prims p)

/-- `vg_<module>_sign`. -/
def sign (p : Params) : Prog isa := scrubAll 32 48 (Sign.sign Sign.prims p)

/-- `vg_<module>_sign_prepared`. -/
def signPrepared (p : Params) : Prog isa := scrubAll 32 48 (Sign.signPrepared Sign.prims p)

/-- `vg_<module>_verify`. -/
def verify (p : Params) : Prog isa := scrubAll 32 56 (Verify.verify Verify.prims p)

/-- `vg_<module>_verify_prepared`. -/
def verifyPrepared (p : Params) : Prog isa := scrubAll 32 56 (Verify.verifyPrepared Verify.prims p)

/-- `vg_<module>_sign_message`, calling `sign` as `signEntryName module`. -/
def signMessage (p : Params) (module : String) : Prog isa :=
  scrubAll 32 56 (Message.signMessage (signEntryName module) (Sign.sign Sign.prims p) p)

/-- `vg_<module>_sign_message_prepared`, calling `sign_prepared` as
`signPreparedEntryName module`. -/
def preparedSignMessage (p : Params) (module : String) : Prog isa :=
  scrubAll 32 56 (Message.signMessage (signPreparedEntryName module) (Sign.signPrepared Sign.prims p) p)

/-- `vg_<module>_verify_message_cached`, calling `verify` as
`verifyEntryName module`. -/
def verifyMessageCached (p : Params) (module : String) : Prog isa :=
  scrubAll 32 56 (Message.verifyMessageCached (verifyEntryName module) (Verify.verify Verify.prims p) p)

/-- `vg_<module>_verify_message_prepared`, calling `verify_prepared` as
`verifyPreparedEntryName module`. -/
def preparedVerifyMessage (p : Params) (module : String) : Prog isa :=
  scrubAll 32 56 (Message.verifyMessageCached (verifyPreparedEntryName module)
    (Verify.verifyPrepared Verify.prims p) p)

end VG.Impl.MlDsa.Arm.Fn
