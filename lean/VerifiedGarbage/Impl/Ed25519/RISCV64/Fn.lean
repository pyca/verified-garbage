module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.KeyPair
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# Ed25519 on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrub`):
the caller-saved registers cleared but the bits of its result (none for key
generation and signing, 32 for verification), and the stack its frames use,
so that it returns without secret residue. Key generation calls SHA-512's
digest, `dg`.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_ed25519_key_pair`, calling SHA-512's digest `dg`. -/
def keyPair (dg : Prog isa) : Prog isa :=
  scrub 0 480 (KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ "_core") dg
    "vg_ed25519_public_key_expanded" Whole.publicKeyExpandedCode)

/-- `vg_ed25519_sign_expanded`. -/
def signExpanded : Prog isa := scrub 0 496 Whole.signExpandedCode

/-- `vg_ed25519_verify`. -/
def verify : Prog isa := scrub 32 480 Whole.verifyCode

end VG.Impl.Ed25519.RISCV64.Fn
