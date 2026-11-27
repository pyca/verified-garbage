module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.KeyGen.Inst
public import VerifiedGarbage.Impl.MlDsa.RISCV64.PkTr
public import VerifiedGarbage.Impl.MlDsa.RISCV64.PreparedKey.Prepare
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Verify.Inst
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Message
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# ML-DSA on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrubAll`):
the caller-saved registers cleared but the bits of its result (none for
`pk_tr` and the preparation of keys, 32 for the others), and the stack its
frames use (1072 to 1184 bytes), so that it returns without secret residue.
Signing and verifying a message call the signing or verification of a
message representative as the internal `vg_mldsa*_sign_core`, … (an `_core`
suffix to each name), whose code is that of the exported functions without
the clearing, so that the stack is cleared once.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- `vg_mldsa44_keygen`. -/
def keyGen44 : Prog isa := scrubAll 32 1168 KeyGen.keyGen44

/-- `vg_mldsa65_keygen`. -/
def keyGen65 : Prog isa := scrubAll 32 1168 KeyGen.keyGen65

/-- `vg_mldsa87_keygen`. -/
def keyGen87 : Prog isa := scrubAll 32 1168 KeyGen.keyGen87

/-- `vg_mldsa44_pk_tr`. -/
def pkTr44 : Prog isa := scrubAll 0 1168 (PkTr.pkTr Spec.MlDsa.mlDsa44)

/-- `vg_mldsa65_pk_tr`. -/
def pkTr65 : Prog isa := scrubAll 0 1168 (PkTr.pkTr Spec.MlDsa.mlDsa65)

/-- `vg_mldsa87_pk_tr`. -/
def pkTr87 : Prog isa := scrubAll 0 1168 (PkTr.pkTr Spec.MlDsa.mlDsa87)

/-- `vg_mldsa44_prepare_verifying_key`. -/
def preparePublic44 : Prog isa := scrubAll 0 1072 (PreparedKey.preparePublic Spec.MlDsa.mlDsa44)

/-- `vg_mldsa44_prepare_signing_key`. -/
def prepareSecret44 : Prog isa := scrubAll 0 1072 (PreparedKey.prepareSecret Spec.MlDsa.mlDsa44)

/-- `vg_mldsa65_prepare_verifying_key`. -/
def preparePublic65 : Prog isa := scrubAll 0 1072 (PreparedKey.preparePublic Spec.MlDsa.mlDsa65)

/-- `vg_mldsa65_prepare_signing_key`. -/
def prepareSecret65 : Prog isa := scrubAll 0 1072 (PreparedKey.prepareSecret Spec.MlDsa.mlDsa65)

/-- `vg_mldsa87_prepare_verifying_key`. -/
def preparePublic87 : Prog isa := scrubAll 0 1072 (PreparedKey.preparePublic Spec.MlDsa.mlDsa87)

/-- `vg_mldsa87_prepare_signing_key`. -/
def prepareSecret87 : Prog isa := scrubAll 0 1072 (PreparedKey.prepareSecret Spec.MlDsa.mlDsa87)

/-- `vg_mldsa44_sign`. -/
def sign44 : Prog isa := scrubAll 32 1184 Sign.sign44

/-- `vg_mldsa44_sign_prepared`. -/
def signPrepared44 : Prog isa := scrubAll 32 1184 (Sign.sign44E true)

/-- `vg_mldsa44_verify`. -/
def verify44 : Prog isa := scrubAll 32 1184 Verify.verify44

/-- `vg_mldsa44_verify_prepared`. -/
def verifyPrepared44 : Prog isa := scrubAll 32 1184 (Verify.verify44E true)

/-- `vg_mldsa44_sign_message`. -/
def signMessage44 : Prog isa :=
  scrubAll 32 1184 (Message.signMessage (Spec.MlDsa.sign44Api.name ++ "_core") Sign.sign44 Spec.MlDsa.mlDsa44)

/-- `vg_mldsa44_sign_message_prepared`. -/
def preparedSignMessage44 : Prog isa :=
  scrubAll 32 1184 (Message.signMessage (s!"vg_{"mldsa44"}_sign_prepared" ++ "_core")
    (Sign.sign44E true) Spec.MlDsa.mlDsa44)

/-- `vg_mldsa44_verify_message_cached`. -/
def verifyMessageCached44 : Prog isa :=
  scrubAll 32 1184 (Message.verifyMessageCached (Spec.MlDsa.verify44Api.name ++ "_core")
    Verify.verify44 Spec.MlDsa.mlDsa44)

/-- `vg_mldsa44_verify_message_prepared`. -/
def preparedVerifyMessage44 : Prog isa :=
  scrubAll 32 1184 (Message.verifyMessageCached (s!"vg_{"mldsa44"}_verify_prepared" ++ "_core")
    (Verify.verify44E true) Spec.MlDsa.mlDsa44)

/-- `vg_mldsa65_sign`. -/
def sign65 : Prog isa := scrubAll 32 1184 Sign.sign65

/-- `vg_mldsa65_sign_prepared`. -/
def signPrepared65 : Prog isa := scrubAll 32 1184 (Sign.sign65E true)

/-- `vg_mldsa65_verify`. -/
def verify65 : Prog isa := scrubAll 32 1184 Verify.verify65

/-- `vg_mldsa65_verify_prepared`. -/
def verifyPrepared65 : Prog isa := scrubAll 32 1184 (Verify.verify65E true)

/-- `vg_mldsa65_sign_message`. -/
def signMessage65 : Prog isa :=
  scrubAll 32 1184 (Message.signMessage (Spec.MlDsa.sign65Api.name ++ "_core") Sign.sign65 Spec.MlDsa.mlDsa65)

/-- `vg_mldsa65_sign_message_prepared`. -/
def preparedSignMessage65 : Prog isa :=
  scrubAll 32 1184 (Message.signMessage (s!"vg_{"mldsa65"}_sign_prepared" ++ "_core")
    (Sign.sign65E true) Spec.MlDsa.mlDsa65)

/-- `vg_mldsa65_verify_message_cached`. -/
def verifyMessageCached65 : Prog isa :=
  scrubAll 32 1184 (Message.verifyMessageCached (Spec.MlDsa.verify65Api.name ++ "_core")
    Verify.verify65 Spec.MlDsa.mlDsa65)

/-- `vg_mldsa65_verify_message_prepared`. -/
def preparedVerifyMessage65 : Prog isa :=
  scrubAll 32 1184 (Message.verifyMessageCached (s!"vg_{"mldsa65"}_verify_prepared" ++ "_core")
    (Verify.verify65E true) Spec.MlDsa.mlDsa65)

/-- `vg_mldsa87_sign`. -/
def sign87 : Prog isa := scrubAll 32 1184 Sign.sign87

/-- `vg_mldsa87_sign_prepared`. -/
def signPrepared87 : Prog isa := scrubAll 32 1184 (Sign.sign87E true)

/-- `vg_mldsa87_verify`. -/
def verify87 : Prog isa := scrubAll 32 1184 Verify.verify87

/-- `vg_mldsa87_verify_prepared`. -/
def verifyPrepared87 : Prog isa := scrubAll 32 1184 (Verify.verify87E true)

/-- `vg_mldsa87_sign_message`. -/
def signMessage87 : Prog isa :=
  scrubAll 32 1184 (Message.signMessage (Spec.MlDsa.sign87Api.name ++ "_core") Sign.sign87 Spec.MlDsa.mlDsa87)

/-- `vg_mldsa87_sign_message_prepared`. -/
def preparedSignMessage87 : Prog isa :=
  scrubAll 32 1184 (Message.signMessage (s!"vg_{"mldsa87"}_sign_prepared" ++ "_core")
    (Sign.sign87E true) Spec.MlDsa.mlDsa87)

/-- `vg_mldsa87_verify_message_cached`. -/
def verifyMessageCached87 : Prog isa :=
  scrubAll 32 1184 (Message.verifyMessageCached (Spec.MlDsa.verify87Api.name ++ "_core")
    Verify.verify87 Spec.MlDsa.mlDsa87)

/-- `vg_mldsa87_verify_message_prepared`. -/
def preparedVerifyMessage87 : Prog isa :=
  scrubAll 32 1184 (Message.verifyMessageCached (s!"vg_{"mldsa87"}_verify_prepared" ++ "_core")
    (Verify.verify87E true) Spec.MlDsa.mlDsa87)

end VG.Impl.MlDsa.RISCV64.Fn
