module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Ed25519 key-pair derivation on PPC64LE

`keyPair dn dg pn pk` (`out`, `expanded`, `seed` and `scratch` in `r3`–`r6`)
writes the seed's SHA-512 digest to `expanded` with the one-shot digest `dg`
(`vg_sha512_digest`, `dn`), and the public key derived from it to `out` with
`pk` (`vg_ed25519_public_key_expanded`, `pn`). A frame of 64 bytes holds,
in its 32 bytes of local variables (at `r1 + 32`, which `r12` points to
before each access, since a call may change `r12`), the link register and
the arguments the second call needs.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE.KeyPair

open VG.PPC64LE

/-- The link register and `out`, `expanded` and `scratch` saved, and the digest's arguments:
`data = seed`, `len = 32`, `out = expanded`. -/
def saveArgs : List Instr :=
  [.mflr .r0, .addSp .r12 32, .store .d .r0 .r12 0, .store .d .r3 .r12 8, .store .d .r4 .r12 16,
    .store .d .r6 .r12 24, .addi .r3 .r5 0, .addi .r5 .r4 0, .li .r4 32]

/-- `public_key_expanded(out, expanded, scratch)`. -/
def pkArgs : List Instr := [.addSp .r12 32, .load .d .r3 .r12 8, .load .d .r4 .r12 16, .load .d .r5 .r12 24]

/-- The link register restored. -/
def restoreLr : List Instr := [.addSp .r12 32, .load .d .r0 .r12 0, .mtlr .r0]

/-- `vg_ed25519_key_pair`: the seed's SHA-512 digest with `dg`, named `dn`, and its
public key from it with `pk`, named `pn` (`keyPairContract`). -/
def keyPair (dn : String) (dg : Prog isa) (pn : String) (pk : Prog isa) : Prog isa :=
  .frame (.alloc 64)
    (.seq (.block saveArgs) (.seq (.call dn dg) (.seq (.block pkArgs) (.seq (.call pn pk) (.block restoreLr)))))
    (.free 64)

end VG.Impl.Ed25519.PPC64LE.KeyPair
