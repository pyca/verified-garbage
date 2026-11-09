module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Top
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on RISC-V: `vg_mldsa44_pk_tr`, `vg_mldsa65_pk_tr`, `vg_mldsa87_pk_tr`

`pkTr p (pk = a0, tr = a1, scratch = a2)`: `tr = H(pk, 64)` (FIPS 204
Algorithm 8, line 6) of the parameter set `p`, as key generation computes
it (`KeyGen.trHash`): it saves our caller's `s3`–`s11` and our return
address in `scratch` at 1288 (as ML-KEM's top-level functions), keeps `pk`
in `s9` (and `s10`, the register of key generation's read-only argument),
`tr` in `s8` and `scratch` in `s11`, and calls the sponge functions, with
the Keccak state at byte 0 of `scratch`, absorbing `pk` in two pieces (its
first 1024 bytes, then the rest), since the length of a piece is an
immediate of 12 bits. Every address and branch depends only on the
pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.PkTr

open VG.RISCV64
open VG.Impl.MlKem.RISCV64 (hash topSave topEnd)
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Spec.MlDsa (Params)

/-- Save our caller's registers in `scratch`, and keep the pointers. -/
def pro : List Instr := topSave .a2 ++ ([mov .s10 .a0, mov .s9 .a0, mov .s8 .a1, mov .s11 .a2] : List Instr)

/-- `tr = H(pk, 64)`. -/
def trHash (p : Params) : Prog isa := hash 136 0x1f [⟨.s9, 0, 1024⟩, ⟨.s9, 1024, p.pkLen - 1024⟩] [⟨.s8, 0, 64⟩]

/-- `vg_mldsa*_pk_tr` for the parameter set `p`. -/
def pkTr (p : Params) : Prog isa := .seq (.block pro) (.seq (trHash p) (.block topEnd))

end VG.Impl.MlDsa.RISCV64.PkTr
