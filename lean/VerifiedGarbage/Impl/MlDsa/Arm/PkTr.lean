module

public import VerifiedGarbage.Impl.MlKem.Arm.Top
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa44_pk_tr`, `vg_mldsa65_pk_tr`, `vg_mldsa87_pk_tr`

`pkTr p (pk = r0, tr = r1, scratch = r2)`: `tr = H(pk, 64)` (FIPS 204
Algorithm 8, line 6) of the parameter set `p`, as key generation computes
it (`KeyGen.trHash`): it saves our caller's `r4`–`r11` and `lr` in
`scratch` at 840 (as ML-KEM's top-level functions), keeps `pk` in `r5` (and
`r4`, the register of key generation's read-only argument), `tr` in `r6`
and `scratch` in `r7`, and calls the sponge functions, with the Keccak
state at byte 0 of `scratch` and their working space at 200. Every address
and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.Arm.PkTr

open VG.Arm
open VG.Impl.MlKem.Arm (hash topEnd saveRegs oSave)
open VG.Spec.MlDsa (Params)

/-- Save our caller's registers in `scratch`, and keep the pointers. -/
def pro : List Instr :=
  saveRegs .r2 oSave ++
    ([.str .lr .r2 (oSave + 32), .mov .r4 (.reg .r0), .mov .r5 (.reg .r0), .mov .r6 (.reg .r1),
      .mov .r7 (.reg .r2)] : List Instr)

/-- `tr = H(pk, 64)`. -/
def trHash (p : Params) : Prog isa := hash 136 0x1f [⟨.r5, 0, p.pkLen⟩] [⟨.r6, 0, 64⟩]

/-- `vg_mldsa*_pk_tr` for the parameter set `p`. -/
def pkTr (p : Params) : Prog isa := .seq (.block pro) (.seq (trHash p) (.block topEnd))

end VG.Impl.MlDsa.Arm.PkTr
