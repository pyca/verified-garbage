module

public import VerifiedGarbage.Impl.Ffdh.RISCV64
public import VerifiedGarbage.Impl.Bignum.RISCV64.ModArith

/-!
# Finite-field Diffie–Hellman on RISC-V: the domain checks

`vg_ffdh_check_public(domain = a0, domain_len = a1, p_len = a2, y = a3,
y_len = a4, scratch = a5, scratch_len = a6)` and
`vg_ffdh_check_domain(domain = a0, domain_len = a1, p_len = a2,
scratch = a3, scratch_len = a4)` (`Spec/Ffdh/Contract.lean`), as PPC64LE's
(`Impl/Ffdh/PPC64LE/Domain.lean`), in the working space of the exchange
(`Impl/Ffdh/RISCV64.lean`): a header of 32 words, then arrays of `w + 2`
words, `w = ⌈p_len / 8⌉`.

* The callee-saved registers are saved in the header's words 16–27, and
  `domain`, `domain_len` and (for `vg_ffdh_check_public`) y in its words
  0–2;
* p is loaded into array 0 and checked as `vg_rsa_public_precompute` checks
  a modulus (`Precompute.check`); otherwise the result is 0;
* a value's `p_len` bytes into array 4 (`PublicChecked.loadX`), and the mask
  of its being in `2 .. p − 2` into `s9` (`range`: the exchange's `zMask`,
  and `PublicChecked.checkX`'s mask of its being below p);
* with q, `R² mod p` into array 1 (`r2`), the value raised to q's `p_len`
  bytes (`ModExp.powWin`) and compared with 1 (`subgroup`);
* `vg_ffdh_check_domain` checks q's range and that it is odd, then that
  `p mod q = 1` (q into array 0, p's bytes reduced modulo q into array 1 by
  `ModArith.reduce64` and compared with 1, then p back into array 0), and g's
  range, before the subgroup.

Everything is public, and the code branches on p's validity, the ranges and
whether there is q. Registers kept throughout: `s6` the working space, `a7`
array 0's base, `s5` an array's size, `t0` `w`, `s11` `p_len`.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.Domain

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base saveRegs restore setup)
open VG.Impl.Ffdh.RISCV64 (loadP r2 eqMask zMask)

/-- The domain into `s7` and `p_len` into `s8` for p's load, and `p_len`
into `a1` for `setup`. -/
def args : List Instr := [.addi .s7 .a0 0, .addi .s8 .a2 0, .addi .a1 .a2 0]

/-- The working space (`a3`) into `t0`, the registers saved there, the domain
and its length into the header's words 0 and 1, then `setup`. -/
def cdFront : List Instr :=
  [.addi .t0 .a3 0] ++ saveRegs ++ [.store .d .a0 .s6 0, .store .d .a1 .s6 8] ++ args ++ setup

/-- As `cdFront`, the working space in `a5`, and y into the header's word 2. -/
def cpFront : List Instr :=
  [.addi .t0 .a5 0] ++ saveRegs ++ [.store .d .a0 .s6 0, .store .d .a1 .s6 8, .store .d .a3 .s6 16] ++ args ++
    setup

/-- `s9 :=` all ones if the `p_len` bytes `v` at `a6` are in `2 .. p − 2`,
else 0: v into array 4, the mask of `v ∉ {0, 1, p − 1}`, and-ed with that of
`v < p`. -/
def range : Prog isa := .seq PublicChecked.loadX (.seq zMask PublicChecked.checkX)

/-- `t3 := domain_len − 3 p_len`: zero exactly when there is q. -/
def hasQ : List Instr :=
  [.load .d .t3 .s6 8, .shift .sll .d .t2 .s11 1, .add .t2 .t2 .s11, .sub .t3 .t3 .t2]

/-- q's bytes (`domain + 2 p_len`) into `s9` and `p_len` into `s10`, for the
power. -/
def qPtr : List Instr := [.load .d .s9 .s6 0, .add .s9 .s9 .s11, .add .s9 .s9 .s11, .addi .s10 .s11 0]

/-- `a0 := 1` if array 4 is 1, else 0: 1 into array 7, and their `eqMask`. -/
def isOne : Prog isa :=
  .seq PublicChecked.one (.seq (.block [.li .s4 (-1)]) (.seq (eqMask 4 7) (.block [.li .a0 1, .logic .and .a0 .a0 .s4])))

/-- `a0 := 1` if `v^q mod p = 1` for v in array 4, else 0: `R² mod p`, the
power by q's bytes, compared with 1. -/
def subgroup : Prog isa := .seq (.seq r2 (.block qPtr)) (.seq ModExp.powWin isOne)

/-- The check of y (its address in the header's word 2), after p's. -/
def checkY : Prog isa :=
  .seq (.block [.load .d .a6 .s6 16]) (.seq range (.ite (.zero .s9) (.block [.li .a0 0])
    (.seq (.block hasQ) (.ite (.zero .t3) subgroup (.block [.li .a0 1])))))

/-- `vg_ffdh_check_public`. -/
def checkPublic : Prog isa :=
  .seq (.block cpFront) (.seq loadP (.seq (.ite (.zero .s0) checkY (.block [.li .a0 0])) (.block restore)))

/-! ## `vg_ffdh_check_domain` -/

/-- `a6 :=` g's bytes, `domain + p_len`. -/
def gPtr : List Instr := [.load .d .a6 .s6 0, .add .a6 .a6 .s11]

/-- `a6 :=` q's bytes, `domain + 2 p_len`. -/
def qPtrA : List Instr := [.load .d .a6 .s6 0, .add .a6 .a6 .s11, .add .a6 .a6 .s11]

/-- `s9 &=` all ones if q (array 4) is odd, else 0. -/
def qOdd : List Instr :=
  base .t3 4 ++ [.load .d .t4 .t3 0, .logicImm .and .t4 .t4 1, .li .t5 0, .sub .t4 .t5 .t4, .logic .and .s9 .s9 .t4]

/-- `s10 :=` all ones if `p mod q = 1`, else 0, for q in array 0: p's bytes
reduced modulo q into array 1, compared with 1 in array 7; then the domain
into `s7` and `p_len` into `s8`, for p's load. -/
def qMask : Prog isa :=
  .seq ModArith.reduce64 (.seq PublicChecked.one (.seq (.block [.li .s4 (-1)]) (.seq (eqMask 1 7)
    (.block [.addi .s10 .s4 0, .load .d .s7 .s6 0, .addi .s8 .s11 0]))))

/-- `s10 :=` all ones if `p mod q = 1`, else 0: q into array 0, `qMask`, then
p back into array 0. -/
def qDiv : Prog isa :=
  .seq (.block [.load .d .s7 .s6 0, .add .s7 .s7 .s11, .add .s7 .s7 .s11, .addi .s8 .s11 0]) (.seq Precompute.loadN
    (.seq (.block [.load .d .s9 .s6 0, .addi .s10 .s11 0]) (.seq qMask Precompute.loadN)))

/-- With q: q's range and oddness, `p mod q = 1`, g's range, then the
subgroup. -/
def withQ : Prog isa :=
  .seq (.block qPtrA) (.seq range (.seq (.block qOdd) (.ite (.zero .s9) (.block [.li .a0 0])
    (.seq qDiv (.seq (.block gPtr) (.seq range (.seq (.block [.logic .and .s9 .s9 .s10])
      (.ite (.zero .s9) (.block [.li .a0 0]) subgroup))))))))

/-- Without q: g's range. -/
def withoutQ : Prog isa :=
  .seq (.block gPtr) (.seq range (.block [.li .a0 1, .logic .and .a0 .a0 .s9]))

/-- The checks after p's. -/
def domainBody : Prog isa := .seq (.block hasQ) (.ite (.zero .t3) withQ withoutQ)

/-- `vg_ffdh_check_domain`. -/
def checkDomain : Prog isa :=
  .seq (.block cdFront) (.seq loadP (.seq (.ite (.zero .s0) domainBody (.block [.li .a0 0])) (.block restore)))

end VG.Impl.Ffdh.RISCV64.Domain
