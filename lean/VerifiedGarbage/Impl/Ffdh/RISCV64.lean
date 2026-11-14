module

public import VerifiedGarbage.Impl.Bignum.RISCV64.ModExp

/-!
# Finite-field Diffie–Hellman on RISC-V: the exchange

`vg_ffdh_exchange(out = a0, out_len = a1, domain = a2, domain_len = a3,
p_len = a4, x = a5, x_len = a6, peer = a7, peer_len, scratch,
scratch_len)` (`Spec/Ffdh/Contract.lean`), the last three on the stack, as
PPC64LE's (`Impl/Ffdh/PPC64LE/Domain.lean`), in the working space of RSA's
operations (`Impl/Bignum/RISCV64/PublicChecked.lean`, `ModExp.lean`) at
`scratch`: a header of 32 words, then arrays of `w + 2` words,
`w = ⌈p_len / 8⌉`.

* The callee-saved registers are saved in the header's words 16–27, and
  `out`, x, `x_len` and the peer in its words 0–3;
* p is loaded into array 0 and checked as `vg_rsa_public_precompute` checks
  a modulus (`Precompute.check`); otherwise the result is 0;
* the peer's y into array 4 (`PublicChecked.loadX`), `R² mod p` into array 1
  (`Precompute.r2`, which also leaves `-p⁻¹ mod 2⁶⁴` in `t1`), and
  `z = y^x mod p` into array 4 by `ModExp.powWin` over x's `x_len` bytes,
  whose windows select table entries by masked scans: nothing depends on x
  but its length;
* the mask of `z ∉ {0, 1, p − 1}` (`zMask`: 0 in array 5, 1 in array 7,
  `p − 1` in array 6, and `eqMask` with each), and z's `p_len` bytes under
  it to `out` (`PublicChecked.output`), with the status 1 or 0.

The code branches on p's validity alone.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base saveRegs restore setup)

/-- The working space, the second argument on the stack, into `t0`; the
registers saved there; `out`, x, `x_len` and the peer into the header's
words 0–3, and the domain into `s7` and `p_len` into `s8` for p's load. -/
def exFront : List Instr :=
  [.addSp .t0 8, .load .d .t0 .t0 0] ++ saveRegs ++
    [.store .d .a0 .s6 0, .store .d .a5 .s6 8, .store .d .a6 .s6 16, .store .d .a7 .s6 24,
      .addi .s7 .a2 0, .addi .s8 .a4 0, .addi .a1 .a4 0] ++ setup

/-- p's `p_len` bytes into array 0, and `s0 := 0` exactly when it is a valid
modulus. -/
def loadP : Prog isa := .seq Precompute.loadN Precompute.check

/-- `R² mod p` into array 1, with array 2 the doublings' accumulator and
array 3 their temporary; `t1 := -p⁻¹ mod 2⁶⁴`. -/
def r2 : Prog isa := .seq (.block (base .a2 1 ++ base .a5 2 ++ base .a6 3)) Precompute.r2

/-- The peer's y into array 4, `R² mod p`, then x's address and length into
`s9` and `s10`. -/
def exPre : Prog isa :=
  .seq (.block [.load .d .a6 .s6 24]) (.seq PublicChecked.loadX
    (.seq r2 (.block [.load .d .s9 .s6 8, .load .d .s10 .s6 16])))

/-- `s4 &=` all ones if arrays `j` and `k` are equal (`w` words), else 0:
the OR of their words' differences, zero exactly when they are equal. -/
def eqMask (j k : Nat) : Prog isa :=
  .seq (.block (base .t3 j ++ base .t4 k ++ [.addi .t5 .t0 0, .li .s1 0]))
    (.seq (countLoop .t5 [.load .d .s2 .t3 0, .load .d .s3 .t4 0, .logic .xor .s2 .s2 .s3,
        .logic .or .s1 .s1 .s2, .addi .t3 .t3 8, .addi .t4 .t4 8])
      (.block [.li .s2 0, .sltu .s1 .s2 .s1, .addi .s1 .s1 (-1), .logic .and .s4 .s4 .s1]))

/-- `p − 1` into array 6: p (array 0) copied, its low word's bit 0 cleared,
as p is odd. -/
def pMinus1 : Prog isa :=
  .seq (.block (base .t3 6 ++ [.addi .t4 .a7 0])) (.seq Precompute.copyWords
    (.block (base .t3 6 ++ [.load .d .s0 .t3 0, .logicImm .xor .s0 .s0 1, .store .d .s0 .t3 0])))

/-- `s9 :=` all ones if z (array 4) is not 0, 1 or `p − 1`, else 0: 0 in
array 5, 1 in array 7, `p − 1` in array 6, and each compared with z, the
masks of equality inverted and anded. -/
def zMask : Prog isa :=
  .seq (.block (base .t3 5)) (.seq Precompute.zeroWords (.seq PublicChecked.one (.seq pMinus1
    (.seq (.block [.li .s9 (-1), .li .s4 (-1)]) (.seq (eqMask 4 5)
      (.seq (.block [.logic .xor .s4 .s4 .s9, .logic .and .s9 .s9 .s4, .li .s4 (-1)]) (.seq (eqMask 4 7)
        (.seq (.block [.logicImm .xor .s4 .s4 (-1), .logic .and .s9 .s9 .s4, .li .s4 (-1)]) (.seq (eqMask 4 6)
          (.block [.logicImm .xor .s4 .s4 (-1), .logic .and .s9 .s9 .s4]))))))))))

/-- z's `p_len` bytes to `out` under the mask, `a0 :=` 1 or 0. -/
def exOut : Prog isa :=
  .seq zMask (.seq (.block [.load .d .s10 .s6 0]) PublicChecked.output)

/-- `vg_ffdh_exchange`. -/
def exchange : Prog isa :=
  .seq (.block exFront) (.seq loadP
    (.seq (.ite (.zero .s0) (.seq exPre (.seq ModExp.powWin exOut)) (.block [.li .a0 0])) (.block restore)))

end VG.Impl.Ffdh.RISCV64
