module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Derive

/-!
# Finite-field Diffie–Hellman on RISC-V: an imported key pair's check

`vg_ffdh_check_private(domain = a0, domain_len = a1, p_len = a2, y = a3,
y_len = a4, x = a5, x_len = a6, scratch = a7, scratch_len)`
(`Spec/Ffdh/Contract.lean`), `scratch_len` on the stack, as
`vg_ffdh_derive_public` (`Derive.lean`) but for its output: with x in range,
`y` is valid and `y = g^x mod p` exactly when `g^x mod p` is in
`2..p − 2` (powers of a checked generator remain in its q subgroup) and
equals y. The arguments are moved to `vg_ffdh_derive_public`'s registers and
y's address is kept in the header's word 4. There is no output: the
exchange's `out` (the header's word 0, and `s10`) is the working space past
its 24 arrays, which nothing writes. After x's range (`Derive.xRange`,
status 2 out of range):

* `z = g^x mod p` into array 4 (`exPre`, `ModExp.powWin`);
* the mask of `1 < z < p − 1` (`zMask`) and, with y's `p_len` octets loaded
  into array 8, that of `z = y` (`eqMask`); the status is 1 under both masks,
  else 0.

The code branches on p's validity, whether there is q and x's range, which
the status reveals.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.CheckPrivate

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive
open VG.Impl.Bignum.RISCV64.PublicChecked (base saveRegs restore setup)

/-- y's address into the header's word 4, and the domain, its length and
`p_len` into `a2`, `a3` and `a4`, as `vg_ffdh_derive_public` has them; x,
`x_len` and g's address into the header's words 1–3, the domain into `s7`
and `p_len` into `s8` and `a1`. -/
def cpHdr : List Instr :=
  [.store .d .a3 .s6 32, .addi .a4 .a2 0, .addi .a3 .a1 0, .addi .a2 .a0 0, .store .d .a5 .s6 8,
    .store .d .a6 .s6 16, .add .t2 .a2 .a4, .store .d .t2 .s6 24, .addi .s7 .a2 0, .addi .s8 .a4 0,
    .addi .a1 .a4 0]

/-- The exchange's `out`: the working space past its 24 arrays, into `s10`
and the header's word 0. -/
def cpOut : List Instr := [.li .t2 24, .mul .t2 .t2 .s5, .add .s10 .t2 .a7, .store .d .s10 .s6 0]

/-- The working space (`a7`) into `t0`, the registers saved there, the
header, `setup`, and the exchange's `out`. -/
def cpFront : List Instr := [.addi .t0 .a7 0] ++ saveRegs ++ cpHdr ++ setup ++ cpOut

/-- y's address from the header's word 4. -/
def ldY : List Instr := [.load .d .s7 .s6 32]

/-- y's `p_len` octets (at `s7`) into array 8, `a7` back to array 0, and
`s4 :=` all ones. -/
def loadY : Prog isa :=
  .seq (.block (base .a7 8 ++ [.addi .s8 .s11 0])) (.seq Precompute.loadN (.block [.addi .a7 .s6 hdrBytes, .li .s4 (-1)]))

/-- `a0 :=` 1 under the masks of `1 < z < p − 1` (`s9`) and `z = y` (`s4`),
else 0. -/
def both : List Instr := [.logic .and .s9 .s9 .s4, .li .a0 1, .logic .and .a0 .a0 .s9]

/-- With z in array 4: the mask of `1 < z < p − 1`, y into array 8 and the
mask of `z = y`; `a0 :=` 1 or 0. -/
def cpCmp : Prog isa := .seq zMask (.seq (.block ldY) (.seq loadY (.seq (eqMask 4 8) (.block both))))

/-- x in range: `a0 :=` 1 if `g^x mod p` is in `2..p − 2` and equals y, else 0. -/
def cpGood : Prog isa := .seq exPre (.seq ModExp.powWin cpCmp)

/-- After p's check. -/
def cpBody : Prog isa := .seq xRange (.ite (.zero .s9) (.block [.li .a0 2]) cpGood)

/-- `vg_ffdh_check_private`. -/
def checkPrivate : Prog isa :=
  .seq (.block cpFront) (.seq loadP
    (.seq (.ite (.zero .s0) cpBody (.block [.li .a0 0])) (.block restore)))

end VG.Impl.Ffdh.RISCV64.CheckPrivate
