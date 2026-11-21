module

public import VerifiedGarbage.Impl.Ed25519.X86.KeyPair
public import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
public import VerifiedGarbage.Impl.Ed25519.X86.SignCached
public import VerifiedGarbage.Impl.Ed25519.X86.VerifyMessage
public import VerifiedGarbage.Impl.MdStream.X86.Digest
public import VerifiedGarbage.Impl.Sha512.X86.Stream
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Spec.Sha512

/-!
# Ed25519 on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Ed25519.X86.Fn

open VG.X86

/-- `vg_sha512_digest_core`, the SHA-512 digest `vg_ed25519_key_pair` calls:
SHA-512's streaming functions (`Impl.Sha512.X86.Stream`) in
`Impl.MdStream.X86.Digest`. -/
def sha512Digest : Prog isa :=
  Impl.MdStream.X86.Digest.digest ⟨128, 192, 64, 64, 34, "vg_sha512_init_core",
    Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512, "vg_sha512_update_scratch",
    Impl.Sha512.X86.Stream.update, "vg_sha512_finalize_scratch", Impl.Sha512.X86.Stream.finalize⟩

/-- `vg_ed25519_key_pair`, as emitted. -/
def keyPair : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 628
    (Impl.Ed25519.X86.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ "_core") sha512Digest
      "vg_ed25519_public_key_expanded" Impl.Ed25519.X86.PublicKey.publicKeyExpanded)

/-- `vg_ed25519_sign_expanded`, as emitted. -/
def signExpanded : Prog isa := Impl.Scrub.X86.scrubAll 0 280 Impl.Ed25519.X86.SignCached.codeExpanded

/-- `vg_ed25519_verify`, as emitted. -/
def verify : Prog isa := Impl.Scrub.X86.scrubAll 32 280 Impl.Ed25519.X86.VerifyMessage.code

end VG.Impl.Ed25519.X86.Fn
