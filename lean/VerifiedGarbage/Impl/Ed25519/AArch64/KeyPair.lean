module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Ed25519 key-pair derivation on AArch64

`keyPair dn dg pn pk (out = x0, expanded = x1, seed = x2, scratch = x3)`
writes the seed's SHA-512 digest to `expanded` with the one-shot digest `dg`
(`vg_sha512_digest` with its suffix, `dn`), and the public key derived from it
to `out` with `pk` (`vg_ed25519_public_key_expanded`, `pn`).

It saves `x30` in a frame of its own, and `out`, `expanded` and `scratch` at
`sp`, `sp + 8` and `sp + 16` in a 32-byte allocation below it, across the
first call.
-/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64.KeyPair

open VG.AArch64

/-- `out`, `expanded` and `scratch` into the allocation, then
`digest(data = seed, len = 32, out = expanded)`. -/
def digestArgs : List Instr :=
  [.strSp .x0 0, .strSp .x1 8, .strSp .x3 16, .addImm .x .x0 .x2 0, .addImm .x .x2 .x1 0,
    .movz .x .x1 32 0]

/-- `public_key_expanded(out, expanded, scratch)`, from the allocation. -/
def pkArgs : List Instr := [.ldrSp .x0 0, .ldrSp .x1 8, .ldrSp .x2 16]

/-- `vg_ed25519_key_pair`: the seed's SHA-512 digest with `dg`, named `dn`, and its
public key from it with `pk`, named `pn` (`keyPairContract`). -/
def keyPair (dn : String) (dg : Prog isa) (pn : String) (pk : Prog isa) : Prog isa :=
  .frame (.push .x30)
    (.frame (.alloc 32)
      (.seq (.block digestArgs) (.seq (.call dn dg) (.seq (.block pkArgs) (.call pn pk))))
      (.free 32))
    (.pop .x30)

end VG.Impl.Ed25519.AArch64.KeyPair
