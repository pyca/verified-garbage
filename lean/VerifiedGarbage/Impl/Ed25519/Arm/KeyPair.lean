module

public import VerifiedGarbage.TCB.Arm.Isa

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
