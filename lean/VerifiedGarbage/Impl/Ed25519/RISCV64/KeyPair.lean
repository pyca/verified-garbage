module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Ed25519 key-pair derivation on RISC-V

`keyPair dn dg pn pk` (`out`, `expanded`, `seed` and `scratch` in `a0`–`a3`)
writes the seed's SHA-512 digest to `expanded` with the one-shot digest `dg`
(`vg_sha512_digest`, `dn`), and the public key derived from it to `out` with
`pk` (`vg_ed25519_public_key_expanded`, `pn`). A frame of 32 bytes (at `sp`,
which `t0` points to before each access, since a call may change `t0`) holds
the return address and the arguments the second call needs.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64.KeyPair

open VG.RISCV64

/-- The return address and `out`, `expanded` and `scratch` saved, and the digest's arguments:
`data = seed`, `len = 32`, `out = expanded`. -/
def saveArgs : List Instr :=
  [.addSp .t0 0, .store .d .ra .t0 0, .store .d .a0 .t0 8, .store .d .a1 .t0 16, .store .d .a3 .t0 24,
    .addi .a0 .a2 0, .addi .a2 .a1 0, .li .a1 32]

/-- `public_key_expanded(out, expanded, scratch)`. -/
def pkArgs : List Instr := [.addSp .t0 0, .load .d .a0 .t0 8, .load .d .a1 .t0 16, .load .d .a2 .t0 24]

/-- The return address restored. -/
def restoreRa : List Instr := [.addSp .t0 0, .load .d .ra .t0 0]

/-- `vg_ed25519_key_pair`: the seed's SHA-512 digest with `dg`, named `dn`, and its
public key from it with `pk`, named `pn` (`keyPairContract`). -/
def keyPair (dn : String) (dg : Prog isa) (pn : String) (pk : Prog isa) : Prog isa :=
  .frame (.alloc 32)
    (.seq (.block saveArgs) (.seq (.call dn dg) (.seq (.block pkArgs) (.seq (.call pn pk) (.block restoreRa)))))
    (.free 32)

end VG.Impl.Ed25519.RISCV64.KeyPair
