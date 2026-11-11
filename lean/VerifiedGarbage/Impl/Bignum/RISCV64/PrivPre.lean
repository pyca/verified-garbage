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
* `n`'s values, as `vg_rsa_public_precompute` computes them
  (`Precompute.core`, in the working space laid out for `w` words at `X`'s
  base, which leaves `X`'s arrays 4 and 5 as they are), which are zeros if
  `n` is not valid; `R² mod n` from them into `X`'s array 6, zero-extended to
  its `2 w` words (`xIn`).
* For each factor, in its working space (`Crt.setupP`): the factor, its
  `-p⁻¹ mod 2⁶⁴` and `R² mod p` from `R² mod n` (`r2Fast`), written to `pre`
  after `n`'s values, under the mask (`prime`). `pre`'s next word is kept in
  the header's word `oDP`, which this function does not otherwise use.
* `n`'s values in `pre` and-ed with the mask, and the result `mask & 1`
  (`maskN`).

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

/-! ## `R_p² mod p` from `R² mod n`

As PPC64LE's (`Impl/Bignum/PPC64LE/PrivPre.lean`): `vg_rsa_private_crt`
computes `R_p² mod p` by `65 w_p` doublings of 1 (`Crt.r2Prime`). Here
`x = R² mod n` is known (`X`'s array 6, from `Precompute.core`), and for
`p | n`, `x ≡ 2^(128 w)` modulo `p`. Steps of Montgomery reduction
(`chunkStep1`, `S := S R_p⁻¹ - C_i R_p⁻¹`, over `x`'s `K = ⌈w / w_p⌉`
chunks `C_i` of `w_p` words, zero-extended; then `S := S R_p⁻¹` while more
than `2 w_p` of `x`'s `2 w` words are left, `zStep`) give
`-S ≡ x R_p^(-K - Z) = 2^(64 e)` for the `e` words left, `1 ≤ e ≤ 2 w_p`
(`Proof/Bignum/PrimeR2.lean`). Then doublings to `2^(128 w_p)`, or, if
`e ≤ w_p`, to `2^(64 w_p + w_p)` and six Montgomery squares (`r2Fast`).
For factors of half `n`'s words, `e = 2 w_p`: two steps and nothing else.
Every count is of the lengths: `w` from `X`'s array size
(`s11 = 16 (w + 1)`), `w_p` from `t0`. -/

/-- The subtraction of `Crt.chunkStep`: `S := S - T mod p`, for `S` in array
4 and `T` in array 7, `p` added back under the borrow. -/
def subST : Prog isa :=
  .seq (.block (base .t3 4 ++ [.add .t3 .t3 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0] ++
      base .a5 4 ++ base .a6 3 ++ base .a7 7))
  (.seq subMod64 (.seq (.block ([.addi .a7 .ra 0] ++ base .t3 3 ++ base .t4 0))
  (.seq ModArith.addMask64 (.seq (.block (base .t3 4 ++ base .t4 3)) copyN))))

/-- One step of the reduction: the next `w` words of `x` (at `s9`) into
array 6, `T := C 1 R⁻¹` into array 7 and `S := S 1 R⁻¹` (1 in array 1),
`S := S - T mod p` (`subST`); `s10 -= w`, and `t2 :=` 1 if `s10 > 0`, else
0. -/
def chunkStep1 : Prog isa :=
  .seq (.block (base .t3 6 ++ [.addi .t4 .s9 0])) (.seq copyN
  (.seq (.block [.addi .s9 .t4 0]) (.seq (PublicChecked.montOp 7 6 1) (.seq (PublicChecked.montOp 4 4 1)
  (.seq subST
  (.block [.sub .s10 .s10 .t0, .addi .t2 .s10 (-1), .shift .srl .d .t2 .t2 63, .logicImm .xor .t2 .t2 1]))))))

/-- `S := -S mod p`: `S` into array 7, array 4 := 0, then `subST`. -/
def negS : Prog isa :=
  .seq (.block (base .t3 7 ++ base .t4 4)) (.seq copyN
  (.seq (.block (base .t3 4)) (.seq Precompute.zeroWords subST)))

/-- A further reduction: `S := S 1 R⁻¹`; `e := e - w_p` (`s10`), and `t2 :=`
1 if `e > 2 w_p`, else 0. -/
def zStep : Prog isa :=
  .seq (PublicChecked.montOp 4 4 1)
    (.block [.sub .s10 .s10 .t0, .shift .sll .d .t2 .t0 1, .sub .t2 .t2 .s10, .shift .srl .d .t2 .t2 63])

/-- `a1` doublings of array 1 modulo `p`. -/
def dblLoop : Prog isa :=
  .loop (.seq Precompute.doubleMod64 (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)

/-- `R² mod p` in array 1, for `p` in array 0, `-p⁻¹ mod 2⁶⁴` in `t1` and
the bases of arrays 1–3 in `a2`, `a5` and `a6`, from `x = R² mod n` in
`X`'s array 6 (`2 w` words, `x` zero-extended): 1 into array 1, `S := 0`
in array 4, the reduction's `K` steps from `s10 = w` while `s10 > 0`
(`chunkStep1`, the chunks at `s9`), then from `e = s10 + w` the further
ones while `e > 2 w_p` (`zStep`), `-S` (`negS`) into array 1, and the
doublings and squares. -/
def r2Fast : Prog isa :=
  .seq (.block [.addi .t3 .a2 0]) (.seq Precompute.zeroWords
  (.seq (.block ([.li .s0 1, .store .d .s0 .a2 0] ++ base .t3 4)) (.seq Precompute.zeroWords
  (.seq (.block (xb .s9 6 ++ [.shift .srl .d .s10 .s11 4, .addi .s10 .s10 (-1)]))
  (.seq (.loop chunkStep1 (.nonzero .t2))
  (.seq (.block [.shift .srl .d .t2 .s11 4, .addi .t2 .t2 (-1), .add .s10 .s10 .t2, .shift .sll .d .t2 .t0 1,
      .sub .t2 .t2 .s10, .shift .srl .d .t2 .t2 63])
  (.seq (.ite (.nonzero .t2) (.loop zStep (.nonzero .t2)) (.block []))
  (.seq negS
  (.seq (.block (base .t3 1 ++ base .t4 4)) (.seq copyN
  (.seq (.block (base .a2 1 ++ base .a5 2 ++ base .a6 3 ++ [.sub .t2 .t0 .s10, .shift .srl .d .t2 .t2 63]))
    (.ite (.nonzero .t2)
      (.seq (.block [.shift .sll .d .a1 .t0 1, .sub .a1 .a1 .s10, .shift .sll .d .a1 .a1 6])
        (.ite (.nonzero .a1) dblLoop (.block [])))
      (.seq (.block [.sub .a1 .t0 .s10, .shift .sll .d .a1 .a1 6, .add .a1 .a1 .t0]) (.seq dblLoop
        (.seq (.block [.li .s7 6])
          (.loop (.seq (ModExp.sqrOp 1 1 4) (.block [.addi .s7 .s7 (-1)])) (.nonzero .s7)))))))))))))))))

/-- In a factor's working space, the factor from `X`'s array `xj`, its
`-p⁻¹ mod 2⁶⁴` in `t1` and `R² mod p` in array 1 (as `Crt.power`'s
start, but by `r2Fast`); then its `w_p` words (`t0`), and-ed with the mask, to `pre` at the
header's cursor (`oDP`), which is advanced past them. -/
def prime (xj : Nat) : Prog isa :=
  .seq (.block ([.addi .t3 .a7 0] ++ xb .t4 xj)) (.seq copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3))
  (.seq r2Fast
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

/-- `R² mod n`, `pre`'s words `w` to `2 w` (`s5`), into `X`'s array 6,
zero-extended to its `2 w` words, for `t0 = w`. -/
def xIn : Prog isa :=
  .seq (.block (xb .t3 6 ++ [.shift .sll .d .t0 .t0 1])) (.seq Precompute.zeroWords
    (.seq (.block ([.shift .srl .d .t0 .t0 1] ++ xb .t3 6 ++ [.shift .sll .d .t4 .t0 3, .add .t4 .s5 .t4]))
      Precompute.copyWords))

/-- `vg_rsa_private_precompute`. -/
def code : Prog isa :=
  .seq (.block (save ++ args)) (.seq zeroIn (.seq (.block setupX) (.seq Crt.loadX (.seq Crt.checks
  (.seq (.block setupN) (.seq Precompute.core (.seq xIn
  (.seq (.block ([.load .d .t3 .s6 oOut, .load .d .t4 .s6 oNLen, .addi .t4 .t4 7, .shift .srl .d .t4 .t4 3,
      .shift .sll .d .t4 .t4 4, .add .t3 .t3 .t4, .store .d .t3 .s6 oDP] ++ setupP oBP oPLen)) (.seq (prime 4)
  (.seq (.block (setupP oBQ oQLen)) (.seq (prime 5)
  (.seq maskN (.block Crt.restore)))))))))))))

end VG.Impl.Bignum.RISCV64.PrivPre
