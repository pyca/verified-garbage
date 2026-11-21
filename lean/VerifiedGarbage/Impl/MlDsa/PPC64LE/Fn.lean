module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.KeyGen.Inst
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Message
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.PkTr
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.PreparedKey
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Verify.Inst
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# MlDsa on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/MlDsa/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `Spec.MlDsa.keyGen44Api`'s function, as emitted. -/
def keyGen44 : Prog isa :=
  scrubAll 32 48 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.KeyGen.keyGen44)

/-- `Spec.MlDsa.pkTr44Api`'s function, as emitted. -/
def pkTr44 : Prog isa :=
  scrubAll 0 48 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa44)

/-- `(Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function, as emitted. -/
def preparePublic44 : Prog isa :=
  scrubAll 0 144 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa44)

/-- `(Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function, as emitted. -/
def prepareSecret44 : Prog isa :=
  scrubAll 0 144 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa44)

/-- `Spec.MlDsa.sign44Api`'s function, as emitted. -/
def sign44 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Sign.sign44)

/-- `(Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function, as emitted. -/
def signPrepared44 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Sign.signPrepared44)

/-- `Spec.MlDsa.signMessage44Api`'s function, as emitted. -/
def signMessage44 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.signMessage (Spec.MlDsa.sign44Api.name ++ "_core") Impl.MlDsa.PPC64LE.Sign.sign44 Spec.MlDsa.mlDsa44)

/-- `Spec.MlDsa.verify44Api`'s function, as emitted. -/
def verify44 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Verify.verify44)

/-- `(Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function, as emitted. -/
def verifyPrepared44 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Verify.verifyPrepared44)

/-- `(Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function, as emitted. -/
def verifyMessageCached44 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Spec.MlDsa.verify44Api.name ++ "_core") Impl.MlDsa.PPC64LE.Verify.verify44 Spec.MlDsa.mlDsa44)

/-- `Spec.MlDsa.keyGen65Api`'s function, as emitted. -/
def keyGen65 : Prog isa :=
  scrubAll 32 48 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.KeyGen.keyGen65)

/-- `Spec.MlDsa.pkTr65Api`'s function, as emitted. -/
def pkTr65 : Prog isa :=
  scrubAll 0 48 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa65)

/-- `(Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function, as emitted. -/
def preparePublic65 : Prog isa :=
  scrubAll 0 144 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa65)

/-- `(Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function, as emitted. -/
def prepareSecret65 : Prog isa :=
  scrubAll 0 144 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa65)

/-- `Spec.MlDsa.sign65Api`'s function, as emitted. -/
def sign65 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Sign.sign65)

/-- `(Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function, as emitted. -/
def signPrepared65 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Sign.signPrepared65)

/-- `Spec.MlDsa.signMessage65Api`'s function, as emitted. -/
def signMessage65 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.signMessage (Spec.MlDsa.sign65Api.name ++ "_core") Impl.MlDsa.PPC64LE.Sign.sign65 Spec.MlDsa.mlDsa65)

/-- `Spec.MlDsa.verify65Api`'s function, as emitted. -/
def verify65 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Verify.verify65)

/-- `(Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function, as emitted. -/
def verifyPrepared65 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Verify.verifyPrepared65)

/-- `(Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function, as emitted. -/
def verifyMessageCached65 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Spec.MlDsa.verify65Api.name ++ "_core") Impl.MlDsa.PPC64LE.Verify.verify65 Spec.MlDsa.mlDsa65)

/-- `Spec.MlDsa.keyGen87Api`'s function, as emitted. -/
def keyGen87 : Prog isa :=
  scrubAll 32 48 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.KeyGen.keyGen87)

/-- `Spec.MlDsa.pkTr87Api`'s function, as emitted. -/
def pkTr87 : Prog isa :=
  scrubAll 0 48 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa87)

/-- `(Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function, as emitted. -/
def preparePublic87 : Prog isa :=
  scrubAll 0 144 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa87)

/-- `(Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function, as emitted. -/
def prepareSecret87 : Prog isa :=
  scrubAll 0 144 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa87)

/-- `Spec.MlDsa.sign87Api`'s function, as emitted. -/
def sign87 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Sign.sign87)

/-- `(Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function, as emitted. -/
def signPrepared87 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Sign.signPrepared87)

/-- `Spec.MlDsa.signMessage87Api`'s function, as emitted. -/
def signMessage87 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.signMessage (Spec.MlDsa.sign87Api.name ++ "_core") Impl.MlDsa.PPC64LE.Sign.sign87 Spec.MlDsa.mlDsa87)

/-- `Spec.MlDsa.verify87Api`'s function, as emitted. -/
def verify87 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Verify.verify87)

/-- `(Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function, as emitted. -/
def verifyPrepared87 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Verify.verifyPrepared87)

/-- `(Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function, as emitted. -/
def verifyMessageCached87 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Spec.MlDsa.verify87Api.name ++ "_core") Impl.MlDsa.PPC64LE.Verify.verify87 Spec.MlDsa.mlDsa87)

/-- `vg_mldsa44_sign_message_prepared`, as emitted. -/
def preparedSignMessage44 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.signMessage (s!"vg_{"mldsa44"}_sign_prepared" ++ "_core")
        Impl.MlDsa.PPC64LE.Sign.signPrepared44 Spec.MlDsa.mlDsa44)

/-- `vg_mldsa44_verify_message_prepared`, as emitted. -/
def preparedVerifyMessage44 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.verifyMessageCached (s!"vg_{"mldsa44"}_verify_prepared" ++ "_core")
        Impl.MlDsa.PPC64LE.Verify.verifyPrepared44 Spec.MlDsa.mlDsa44)

/-- `vg_mldsa65_sign_message_prepared`, as emitted. -/
def preparedSignMessage65 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.signMessage (s!"vg_{"mldsa65"}_sign_prepared" ++ "_core")
        Impl.MlDsa.PPC64LE.Sign.signPrepared65 Spec.MlDsa.mlDsa65)

/-- `vg_mldsa65_verify_message_prepared`, as emitted. -/
def preparedVerifyMessage65 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.verifyMessageCached (s!"vg_{"mldsa65"}_verify_prepared" ++ "_core")
        Impl.MlDsa.PPC64LE.Verify.verifyPrepared65 Spec.MlDsa.mlDsa65)

/-- `vg_mldsa87_sign_message_prepared`, as emitted. -/
def preparedSignMessage87 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.signMessage (s!"vg_{"mldsa87"}_sign_prepared" ++ "_core")
        Impl.MlDsa.PPC64LE.Sign.signPrepared87 Spec.MlDsa.mlDsa87)

/-- `vg_mldsa87_verify_message_prepared`, as emitted. -/
def preparedVerifyMessage87 : Prog isa :=
  scrubAll 32 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (Impl.MlDsa.PPC64LE.Message.verifyMessageCached (s!"vg_{"mldsa87"}_verify_prepared" ++ "_core")
        Impl.MlDsa.PPC64LE.Verify.verifyPrepared87 Spec.MlDsa.mlDsa87)

end VG.Impl.MlDsa.PPC64LE.Fn
