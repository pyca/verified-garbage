module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# Ed25519 key-pair derivation on x86

`keyPair dn dg pn pk` (cdecl: `out`, `expanded`, `seed` and `scratch` at
`esp + 4`, `+ 8`, `+ 12` and `+ 16`) writes the seed's SHA-512 digest to
`expanded` with the one-shot digest `dg` (`vg_sha512_digest`, `dn`), and the
public key derived from it to `out` with `pk`
(`vg_ed25519_public_key_expanded`, `pn`). Each callee's three arguments are
pushed in a frame of their own around its call, which leaves `esp` 16-byte
aligned at both calls; the function's own arguments stay where they are, so
it needs no frame of its own.
-/

@[expose] public section

namespace VG.Impl.Ed25519.X86.KeyPair

open VG.X86

/-- `[esp + d]`. -/
def at_ (d : Nat) : MemOp := { base := .esp, disp := d }

/-- The registers of a callee's arguments, pushed last-first: `eax` is the first. -/
def argRegs : List Reg := [.edx, .ecx, .eax]

/-- `digest(data = seed, len = 32, out = expanded)`. -/
def digestArgs : List Instr := [.mov .eax (.mem (at_ 12)), .mov .ecx (.imm 32), .mov .edx (.mem (at_ 8))]

/-- `public_key_expanded(out, expanded, scratch)`. -/
def pkArgs : List Instr := [.mov .eax (.mem (at_ 4)), .mov .ecx (.mem (at_ 8)), .mov .edx (.mem (at_ 16))]

/-- `vg_ed25519_key_pair`: the seed's SHA-512 digest with `dg`, named `dn`, and its
public key from it with `pk`, named `pn` (`keyPairContract`). -/
def keyPair (dn : String) (dg : Prog isa) (pn : String) (pk : Prog isa) : Prog isa :=
  .seq (.block digestArgs) (.seq (.frame (.push argRegs) (.call dn dg) (.pop .eax 3))
    (.seq (.block pkArgs) (.frame (.push argRegs) (.call pn pk) (.pop .eax 3))))

end VG.Impl.Ed25519.X86.KeyPair
