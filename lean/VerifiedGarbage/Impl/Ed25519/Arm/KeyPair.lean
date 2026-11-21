module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Impl.Ed25519.Arm.PublicKey
public import VerifiedGarbage.Impl.MdStream.Arm.Digest
public import VerifiedGarbage.Impl.Sha512.Arm.Stream
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# Ed25519 key-pair derivation on ARMv7

`keyPair dn dg pn pk (out = r0, expanded = r1, seed = r2, scratch = r3)` writes
the seed's SHA-512 digest to `expanded` with the one-shot digest `dg`
(`vg_sha512_digest`, `dn`), and the public key derived from it to `out` with
`pk` (`vg_ed25519_public_key_expanded`, `pn`).

It saves `lr` in a frame of its own and, below it, `out`, `expanded` and
`scratch` (`r0`, `r1` and `r3`, at `sp`, `sp + 4` and `sp + 8`) across the
first call: 16 bytes, which keep `sp` 8-byte aligned at both calls.
-/

@[expose] public section

namespace VG.Impl.Ed25519.Arm.KeyPair

open VG.Arm

/-- `digest(data = seed, len = 32, out = expanded)`. -/
def digestArgs : List Instr := [.mov .r0 (.reg .r2), .ldrSp .r2 4, .movw .r1 32]

/-- `public_key_expanded(out, expanded, scratch)`, from the frame. -/
def pkArgs : List Instr := [.ldrSp .r0 0, .ldrSp .r1 4, .ldrSp .r2 8]

/-- `vg_ed25519_key_pair`: the seed's SHA-512 digest with `dg`, named `dn`, and its
public key from it with `pk`, named `pn` (`keyPairContract`). -/
def keyPair (dn : String) (dg : Prog isa) (pn : String) (pk : Prog isa) : Prog isa :=
  .frame (.push [.lr])
    (.frame (.push [.r0, .r1, .r3])
      (.seq (.block digestArgs) (.seq (.call dn dg) (.seq (.block pkArgs) (.call pn pk))))
      (.pop .r3 12))
    (.pop .lr 4)

end VG.Impl.Ed25519.Arm.KeyPair

namespace VG.Impl.Ed25519.Arm.KeyPair

/-- SHA-512 by its streaming functions, as `vg_sha512_digest` computes it
(`Impl.MdStream.Arm.Digest`): the seed's digest that `vg_ed25519_key_pair`
calls. -/
def sha512 : Impl.Pbkdf2.Stream.Arm.Hash :=
  ⟨128, 192, 64, 64, 34, "vg_sha512_init_core", Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512,
    "vg_sha512_update_scratch", Impl.Sha512.Arm.Stream.update, "vg_sha512_finalize_scratch",
    Impl.Sha512.Arm.Stream.finalize⟩

end VG.Impl.Ed25519.Arm.KeyPair

namespace VG.Impl.Ed25519.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ed25519_key_pair`, with either product of the field (`umaal`): the
digest by `vg_sha512_digest`'s code, called as the internal
`vg_sha512_digest_core`, and the public key by
`vg_ed25519_public_key_expanded` (with `umaal`,
`vg_ed25519_public_key_expanded_umaal`); then the 600 bytes of stack its
contract reserves zeroed and the registers a callee may change set to
constants. -/
def keyPair (umaal : Bool) : Prog isa :=
  scrubAll 0 600 (KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ "_core")
    (Impl.MdStream.Arm.Digest.digest KeyPair.sha512) ("vg_ed25519_public_key_expanded" ++ suffix umaal)
    (PublicKey.codeExpanded umaal))

end VG.Impl.Ed25519.Arm.Fn
