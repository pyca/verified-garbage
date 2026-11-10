module

public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt

/-!
# An RSA private key's precomputed values on RISC-V

`vg_rsa_private_precompute(pre = a0, pre_len = a1, n = a2, n_len = a3,
p = a4, p_len = a5, q = a6, q_len = a7, scratch, scratch_len)`, the last two
on the stack: with the modulus `n` (`k = n_len` bytes) of `w = ⌈k / 8⌉`
words and its factors `p` and `q`, writes `n` and `R² mod n` (`w` words
each), then `R_p² mod p` (`w_p = max(2, ⌈p_len / 8⌉)` words) and
`R_q² mod q` to `pre` and returns 1 if `n` is valid and `p q = n`, and
otherwise writes zeros and returns 0. As PPC64LE's
(`Impl/Bignum/PPC64LE/PrivPre.lean`):

* The checks, in `vg_rsa_private_crt`'s working space `X` with its header
  (`Crt.lean`), by its own code (`Crt.loadX`, `Crt.checks`), with `pre` as
  the input and as `qInv`, its first `2 ⌈k / 8⌉` words zeroed first
  (`zeroIn`): the mask (`s9`, and the header's `oMask`) of `n` valid,
  `0 < n`, `0 < p` and `p q = n`, which is that of `n` valid and `p q = n`;
  `p` and `q` kept under the mask, else 3.
* For each factor, in its working space (`Crt.setupP`): the factor, its
  `-p⁻¹ mod 2⁶⁴` and `R² mod p` (`Crt.r2Prime`), as `vg_rsa_private_crt`'s
  `power` computes them, written to `pre` after `n`'s values, under the mask
  (`prime`). `pre`'s next word is kept in the header's word `oDP`, which
  this function does not otherwise use.
* `n`'s values, as `vg_rsa_public_precompute` computes them
  (`Precompute.core`, in the working space laid out for `w` words), which
  are zeros if `n` is not valid; then and-ed with the mask, and the result
  `mask & 1` (`maskN`).

Nothing branches on `p` or `q`: the loops count lengths, and the code
branches only on `n`'s validity (in `Precompute.core`).

The header holds `vg_rsa_private_crt`'s words that the checks and
`Crt.setupP` read (`oN`, `oNLen`, `oP`, `oPLen`, `oQ`, `oQLen`, `oBP`,
`oBQ`, `oMask`), `pre` at `oOut` and its cursor at `oDP`, and the
callee-saved registers and `ra` from byte 112, as `vg_rsa_private_crt`'s.
-/

@[expose] public section

namespace VG.Impl.Bignum.RISCV64.PrivPre

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-- The working space's address, the first stack argument, into `t0`; the
registers saved there (as `Crt.save`), and its address into `s6`. -/
def save : List Instr :=
  [.addSp .t0 0, .load .d .t0 .t0 0] ++
    (List.range 13).flatMap (fun i => [.store .d (Crt.saved i) .t0 (Crt.savOff i)]) ++ [.addi .s6 .t0 0]

/-- The arguments into the header, `pre` also as the input (`oIn`) and as
`qInv` (`oQInv`) for `Crt.checks`, which finds them zero. -/
def args : List Instr :=
  [.store .d .a0 .s6 oOut, .store .d .a2 .s6 oN, .store .d .a3 .s6 oNLen, .store .d .a0 .s6 oIn,
    .store .d .a4 .s6 oP, .store .d .a5 .s6 oPLen, .store .d .a6 .s6 oQ, .store .d .a7 .s6 oQLen,
    .store .d .a0 .s6 oQInv]

/-- `pre`'s first `2 w = 2 ⌈k / 8⌉` words := 0, so that `Crt.checks` reads
the input and `qInv` as 0: its mask is then that of `n` valid and
`p q = n`. -/
def zeroIn : Prog isa :=
  .seq (.block [.addi .t3 .a0 0, .addi .t0 .a3 7, .shift .srl .d .t0 .t0 3, .shift .sll .d .t0 .t0 1])
    Precompute.zeroWords

/-- In a factor's working space, the factor from `X`'s array `xj`, its
`-p⁻¹ mod 2⁶⁴` in `t1` and `R² mod p` in array 1 (as `Crt.power`'s
start); then its `w_p` words (`t0`), and-ed with the mask, to `pre` at the
header's cursor (`oDP`), which is advanced past them. -/
def prime (xj : Nat) : Prog isa :=
  .seq (.block ([.addi .t3 .a7 0] ++ xb .t4 xj)) (.seq copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3))
  (.seq (r2Prime 4)
  (.seq (.block (base .t4 1 ++ [.load .d .t3 .s6 oDP, .load .d .t1 .s6 oMask, .addi .t5 .t0 0]))
  (.seq (countLoop .t5 [.load .d .s0 .t4 0, .logic .and .s0 .s0 .t1, .store .d .s0 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8])
    (.block [.store .d .t3 .s6 oDP]))))))

/-- `Precompute.core`'s registers, for the working space at `s6` (as
`Precompute.setup` but for the header's `w`, which `core` does not read),
from the header. -/
def setupN : List Instr :=
  [.load .d .s5 .s6 oOut, .load .d .s7 .s6 oN, .load .d .s8 .s6 oNLen, .addi .t0 .s8 7, .shift .srl .d .t0 .t0 3,
    .shift .sll .d .a1 .t0 3, .addi .a1 .a1 16, .addi .a7 .s6 hdrBytes, .add .a2 .a7 .a1, .add .a5 .a2 .a1,
    .add .a6 .a5 .a1]

/-- `n`'s `2 w` words in `pre` `&=` the mask, `w = ⌈k / 8⌉`; the result
`mask & 1` into `a0`. -/
def maskN : Prog isa :=
  .seq (.block [.load .d .t3 .s6 oOut, .load .d .t5 .s6 oNLen, .addi .t5 .t5 7, .shift .srl .d .t5 .t5 3,
      .shift .sll .d .t5 .t5 1, .load .d .t1 .s6 oMask])
    (.seq (countLoop .t5 [.load .d .s0 .t3 0, .logic .and .s0 .s0 .t1, .store .d .s0 .t3 0, .addi .t3 .t3 8])
      (.block [.li .a0 1, .logic .and .a0 .a0 .t1]))

/-- `vg_rsa_private_precompute`. -/
def code : Prog isa :=
  .seq (.block (save ++ args)) (.seq zeroIn (.seq (.block setupX) (.seq Crt.loadX (.seq Crt.checks
  (.seq (.block ([.load .d .t3 .s6 oOut, .load .d .t4 .s6 oNLen, .addi .t4 .t4 7, .shift .srl .d .t4 .t4 3,
      .shift .sll .d .t4 .t4 4, .add .t3 .t3 .t4, .store .d .t3 .s6 oDP] ++ setupP oBP oPLen)) (.seq (prime 4)
  (.seq (.block (setupP oBQ oQLen)) (.seq (prime 5)
  (.seq (.block setupN) (.seq Precompute.core (.seq maskN (.block Crt.restore))))))))))))

end VG.Impl.Bignum.RISCV64.PrivPre
