module

public import VerifiedGarbage.Impl.Ed25519.X86_64.PublicKey

/-!
# Ed25519 key-pair derivation on x86-64

`keyPair dn dg pn pk (out = rdi, expanded = rsi, seed = rdx, scratch = rcx)`
writes the seed's SHA-512 digest to `expanded` with the one-shot digest `dg`
(`vg_sha512_digest` with its suffix, `dn`), and the public key derived from it
to `out` with `pk` (`vg_ed25519_public_key_expanded` with its suffix, `pn`).

A frame of three words keeps `out` (`rsp + 16`), `expanded` (`rsp + 8`) and
`scratch` (`rsp`) across the first call; with the return address, it leaves
`rsp` 16-byte aligned at both calls, as the ABI has it.
-/

@[expose] public section

namespace VG.Impl.Ed25519.X86_64.KeyPair

open VG.X86_64
open VG.Impl.Ed25519.X86_64 (stk)

/-- The registers the frame keeps: `out`, `expanded`, `scratch`. -/
def pushRs : List Reg := [.rdi, .rsi, .rcx]

/-- `digest(data = seed, len = 32, out = expanded)`. -/
def digestArgs : List Instr := [.mov .rdi (.reg .rdx), .mov .rdx (.reg .rsi), .mov32 .rsi (.imm 32)]

/-- `public_key_expanded(out, expanded, scratch)`, from the frame. -/
def pkArgs : List Instr :=
  [.mov .rdi (.mem (stk 16)), .mov .rsi (.mem (stk 8)), .mov .rdx (.mem (stk 0))]

/-- `vg_ed25519_key_pair`: the seed's SHA-512 digest with `dg`, named `dn`, and its
public key from it with `pk`, named `pn` (`keyPairContract`). -/
def keyPair (dn : String) (dg : Prog isa) (pn : String) (pk : Prog isa) : Prog isa :=
  .frame (.push pushRs)
    (.seq (.block digestArgs) (.seq (.call dn dg) (.seq (.block pkArgs) (.call pn pk))))
    (.pop .rax 3)

end VG.Impl.Ed25519.X86_64.KeyPair
