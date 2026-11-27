module

public import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Inst
public import VerifiedGarbage.Impl.MlDsa.X86.PkTr
public import VerifiedGarbage.Impl.MlDsa.X86.PreparedKey
public import VerifiedGarbage.Impl.MlDsa.X86.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Impl.MlDsa.X86.Message
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# ML-DSA's functions on x86 (32-bit), as emitted

Each public function of the parameter set `p` (in the module `module`, which
names the functions it calls) is its code, with this library's primitives,
then its cleanup (`Impl.Scrub.X86.scrubAll`): the stack its contract reserves
below `esp` zeroed, then the registers a callee may change cleared, but the
32 bits of its result (`pk_tr` and the preparations of keys return none):

* key generation and the preparations of keys: 96 bytes;
* `pk_tr`: 56;
* `sign`, `sign_prepared`, `verify` and `verify_prepared`: 136;
* `sign_message` and `sign_message_prepared`: 176;
* `verify_message_cached` and `verify_message_prepared`: 172.

The message functions call the functions on `μ` (`vg_<module>_sign`, …) as
they are verified, without the cleanup, under names of their own
(`Sign.entryName`, …), which the emitter writes as internal functions: their
own cleanup covers the frames of those calls.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.Fn

open VG.X86 VG.Impl.Scrub.X86
open VG.Spec.MlDsa (Params)

/-- `vg_<module>_keygen`. -/
def keyGen (p : Params) : Prog isa := scrubAll 32 96 (KeyGen.keyGen KeyGen.prims p)

/-- `vg_<module>_pk_tr`. -/
def pkTr (p : Params) : Prog isa := scrubAll 0 56 (PkTr.pkTr p)

/-- `vg_<module>_prepare_verifying_key`. -/
def preparePublic (p : Params) : Prog isa := scrubAll 0 96 (PreparedKey.preparePublic Verify.prims p)

/-- `vg_<module>_prepare_signing_key`. -/
def prepareSecret (p : Params) : Prog isa := scrubAll 0 96 (PreparedKey.prepareSecret Verify.prims p)

/-- `vg_<module>_sign`. -/
def sign (p : Params) (module : String) : Prog isa := scrubAll 32 136 (Sign.signOf p module)

/-- `vg_<module>_sign_prepared`. -/
def signPrepared (p : Params) (module : String) : Prog isa := scrubAll 32 136 (Sign.signPreparedOf p module)

/-- `vg_<module>_verify`. -/
def verify (p : Params) (module : String) : Prog isa := scrubAll 32 136 (Verify.verifyOf p module)

/-- `vg_<module>_verify_prepared`. -/
def verifyPrepared (p : Params) (module : String) : Prog isa := scrubAll 32 136 (Verify.verifyPreparedOf p module)

/-- `vg_<module>_sign_message`, calling `sign` as `Sign.entryName module`. -/
def signMessage (p : Params) (module : String) : Prog isa :=
  scrubAll 32 176 (Message.signMessage (Sign.entryName module) (Sign.signOf p module) p)

/-- `vg_<module>_sign_message_prepared`, calling `sign_prepared` as
`Sign.preparedEntryName module`. -/
def preparedSignMessage (p : Params) (module : String) : Prog isa :=
  scrubAll 32 176 (Message.signMessage (Sign.preparedEntryName module) (Sign.signPreparedOf p module) p)

/-- `vg_<module>_verify_message_cached`, calling `verify` as
`Verify.entryName module`. -/
def verifyMessageCached (p : Params) (module : String) : Prog isa :=
  scrubAll 32 172 (Message.verifyMessageCached (Verify.entryName module) (Verify.verifyOf p module) p)

/-- `vg_<module>_verify_message_prepared`, calling `verify_prepared` as
`Verify.preparedEntryName module`. -/
def preparedVerifyMessage (p : Params) (module : String) : Prog isa :=
  scrubAll 32 172 (Message.verifyMessageCached (Verify.preparedEntryName module) (Verify.verifyPreparedOf p module) p)

end VG.Impl.MlDsa.X86.Fn
