module

public import VerifiedGarbage.Impl.Ffdh.RISCV64

/-!
# Finite-field Diffie–Hellman on RISC-V: a private key's public value

`vg_ffdh_derive_public(y = a0, y_len = a1, domain = a2, domain_len = a3,
p_len = a4, x = a5, x_len = a6, scratch = a7, scratch_len)`
(`Spec/Ffdh/DerivePublicContract.lean`), `scratch_len` on the stack, in the
working space of `vg_ffdh_exchange` (`Impl/Ffdh/RISCV64.lean`), with `y` as
its `out` and g (at `domain + p_len`) as its peer, kept in the header's words
0–3 with x and `x_len`:

* p is loaded into array 0 and checked as the exchange checks it; otherwise
  the result is 0;
* x's `x_len` octets into array 4 (`PublicChecked.loadX`), the bound into
  array 1 (q's `p_len` octets at `domain + 2 p_len`) or array 6 (`p − 1`,
  without q); the mask of x below it is `subMod64`'s, and that of `x = 0`
  `eqMask`'s with 0 in array 5 (`xRange`);
* out of range, the status is 2 and `y` gets zeros, by
  `PublicChecked.output` under the zero mask;
* otherwise `y = g^x mod p` as the exchange computes its shared value,
  written to `y` under the mask of `1 < y < p − 1` or replaced by zeros, and
  the status `3 − 2 a0`: 1 or 3.

The code branches on p's validity, whether there is q and x's range, which
the status reveals.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.Derive

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base saveRegs restore setup)

/-- The working space (`a7`) into `t0`; the registers saved there; `y`, x,
`x_len` and g's address into the header's words 0–3, and the domain into
`s7` and `p_len` into `s8` for p's load. -/
def dpFront : List Instr :=
  [.addi .t0 .a7 0] ++ saveRegs ++
    [.store .d .a0 .s6 0, .store .d .a5 .s6 8, .store .d .a6 .s6 16, .add .t2 .a2 .a4,
      .store .d .t2 .s6 24, .addi .s7 .a2 0, .addi .s8 .a4 0, .addi .a1 .a4 0] ++ setup

/-- x's `x_len` octets (at `a5`, the length in `a6`) into array 4, through
`loadX` with the length in `s11`. -/
def xLoad : Prog isa := .seq (.block [.addi .s11 .a6 0, .addi .a6 .a5 0]) PublicChecked.loadX

/-- The comparison's arrays: x (array 4) and its temporary (array 3); and
`t2 := 0` exactly when `domain_len = 3 p_len`: there is q. -/
def xPrep : List Instr :=
  base .a5 4 ++ base .a6 3 ++ [.add .t2 .a4 .a4, .add .t2 .t2 .a4, .sub .t2 .a3 .t2]

/-- `a7 :=` the bound's array: q's octets loaded into array 1, or `p − 1`
in array 6 without q. -/
def xBound : Prog isa :=
  .ite (.zero .t2)
    (.seq (.block (base .a7 1 ++ [.add .s7 .a4 .a4, .add .s7 .s7 .a2, .addi .s8 .a4 0])) Precompute.loadN)
    (.seq pMinus1 (.block (base .a7 6)))

/-- The end of the range: `s9 &=` the inverted mask of `x = 0`; the
registers of the domain and `p_len` back, and `s0 := 0`. -/
def xFin : List Instr :=
  [.logicImm .xor .s4 .s4 (-1), .logic .and .s9 .s9 .s4, .addi .s7 .a2 0, .addi .s8 .a4 0,
    .addi .s11 .a4 0, .li .s0 0]

/-- `s9 :=` the mask of x below the bound (`subMod64`'s), then that of
`x ≠ 0` and'ed in, with 0 in array 5. -/
def xCmp : Prog isa :=
  .seq subMod64 (.seq (.block ([.addi .a7 .s6 hdrBytes, .addi .s9 .s4 0] ++ base .t3 5))
    (.seq Precompute.zeroWords (.seq (.block [.li .s4 (-1)]) (.seq (eqMask 4 5) (.block xFin)))))

/-- x into array 4, and `s9 :=` all ones if `0 < x < bound`, else 0. -/
def xRange : Prog isa := .seq xLoad (.seq (.block xPrep) (.seq xBound xCmp))

/-- x out of range: zeros to `y`, status 2. -/
def dpBad : Prog isa := .seq PublicChecked.output (.block [.li .a0 2])

/-- `a0 := 3 − 2 a0`. -/
def status : List Instr := [.shift .sll .d .a0 .a0 1, .li .t2 3, .sub .a0 .t2 .a0]

/-- x in range: `g^x mod p` to `y` or zeros, status 1 or 3. -/
def dpGood : Prog isa := .seq exPre (.seq ModExp.powWin (.seq exOut (.block status)))

/-- After p's check. -/
def dpBody : Prog isa := .seq xRange (.ite (.zero .s9) dpBad dpGood)

/-- `vg_ffdh_derive_public`. -/
def derivePublic : Prog isa :=
  .seq (.block dpFront) (.seq loadP
    (.seq (.ite (.zero .s0) dpBody (.block [.li .a0 0])) (.block restore)))

end VG.Impl.Ffdh.RISCV64.Derive
