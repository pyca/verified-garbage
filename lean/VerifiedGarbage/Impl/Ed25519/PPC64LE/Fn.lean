module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.KeyPair
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.Impl.MdStream.PPC64LE.Digest
public import VerifiedGarbage.Spec.Sha512

/-!
# Ed25519 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Ed25519/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_ed25519_key_pair`, as emitted: it calls SHA-512's digest as
`vg_sha512_digest_core` and `vg_ed25519_public_key_expanded`. -/
def keyPair : Prog isa :=
  scrubAll 0 720 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.Ed25519.PPC64LE.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ "_core")
      (Impl.MdStream.PPC64LE.Digest.code Impl.Hmac.Stream.PPC64LE.sha512Hash) "vg_ed25519_public_key_expanded"
      Impl.Ed25519.PPC64LE.Whole.publicKeyExpandedCode)

/-- `vg_ed25519_sign_expanded`, as emitted. -/
def signExpanded : Prog isa :=
  scrubAll 0 320 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.Ed25519.PPC64LE.Whole.signExpandedCode)

/-- `vg_ed25519_verify`, as emitted. -/
def verify : Prog isa :=
  scrubAll 32 224 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.Ed25519.PPC64LE.Whole.verifyCode)

end VG.Impl.Ed25519.PPC64LE.Fn
