module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt

/-!
# An RSA private key's precomputed values on PPC64LE

`vg_rsa_private_precompute(pre = r3, pre_len = r4, n = r5, n_len = r6,
p = r7, p_len = r8, q = r9, q_len = r10, scratch, scratch_len)`, the last two
on the stack: with the modulus `n` (`k = n_len` bytes) of `w = ⌈k / 8⌉`
words and its factors `p` and `q`, writes `n` and `R² mod n` (`w` words
each), then `R_p² mod p` (`w_p = max(2, ⌈p_len / 8⌉)` words) and
`R_q² mod q` to `pre` and returns 1 if `n` is valid and `p q = n`, and
otherwise writes zeros and returns 0.

* The checks, in `vg_rsa_private_crt`'s working space `X` with its header
  (`Crt.lean`), by its own code (`Crt.loadX`, `Crt.checks`), with `pre` as
  the input and as `qInv`, its first `⌈k / 8⌉` words zeroed first
  (`zeroIn`): the mask `r26` of `n` valid, `0 < n`, `0 < p` and `p q = n`,
  which is that of `n` valid and `p q = n`; `p` and `q` kept under the mask,
  else 3.
* For each factor, in its working space (`Crt.setupP`): the factor, its
  `-p⁻¹ mod 2³²` and `R² mod p` (`Precompute.r2Prime`), as
  `vg_rsa_private_crt`'s `power` computes them, written to `pre` after `n`'s
  values, under the mask.
* `n`'s values, as `vg_rsa_public_precompute` computes them
  (`Precompute.core`, in the working space laid out for `w` words), which
  are zeros if `n` is not valid; then and-ed with the mask, and the result
  `r26 & 1`.

Nothing branches on `p` or `q`: the loops count lengths, and the code
branches only on `n`'s validity (in `Precompute.core`).

The header holds `vg_rsa_private_crt`'s words that the checks and
`Crt.setupP` read (`oN`, `oNLen`, `oP`, `oPLen`, `oQ`, `oQLen`, `oBP`,
`oBQ`), `pre` at `oOut`, and the nonvolatile registers from byte 112, as
`vg_rsa_private_crt`'s.
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE.PrivPre

open VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt

/-- The working space's address, the first argument on the stack, into
`r11`; the registers saved there (as `Crt.save`), and its address into
`r23`. -/
def save : List Instr :=
  [.addSp .r11 96, .load .d .r11 .r11 0] ++
    (List.range 18).flatMap (fun i => [.store .d (Crt.saved i) .r11 (Crt.savOff i)]) ++ [.addi .r23 .r11 0]

/-- The arguments into the header, `pre` also as the input (`oIn`) and as
`qInv` (`oQInv`) for `Crt.checks`, which finds them zero. -/
def args : List Instr :=
  [.store .d .r3 .r23 oOut, .store .d .r5 .r23 oN, .store .d .r6 .r23 oNLen, .store .d .r3 .r23 oIn,
    .store .d .r7 .r23 oP, .store .d .r8 .r23 oPLen, .store .d .r9 .r23 oQ, .store .d .r10 .r23 oQLen,
    .store .d .r3 .r23 oQInv]

/-- `pre`'s first `w = ⌈k / 8⌉` words := 0, so that `Crt.checks` reads the
input and `qInv` as 0: its mask is then that of `n` valid and `p q = n`. -/
def zeroIn : Prog isa :=
  .seq (.block [.addi .r14 .r3 0, .addi .r11 .r6 7, .lsr .d .r11 .r11 3, .lsl .r11 .r11 1]) Precompute.zeroWords

/-- In a factor's working space, the factor from `X`'s array `xj`, its
`-p⁻¹ mod 2³²` in `r12` and `R² mod p` in array 1 (as `Crt.power`'s
start); then its `w_p` words (`r11 / 2`), and-ed with the mask, to `pre` at
`r30`, which is advanced past them. -/
def prime (xj : Nat) : Prog isa :=
  .seq (.block ([.addi .r14 .r10 0] ++ xb .r15 xj)) (.seq copyN
  (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++
      PublicChecked.base .r9 3))
  (.seq Precompute.r2Prime
  (.seq (.block (PublicChecked.base .r15 1 ++ [.lsr .d .r17 .r11 1]))
    (Precompute.countLoop .r17 [.load .d .r0 .r15 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r30 0,
      .addi .r15 .r15 8, .addi .r30 .r30 8])))))

/-- `Precompute.core`'s registers, for the working space at `r23` (as
`Precompute.setup` but for the header's `w`, which `core` does not read),
from the header. -/
def setupN : List Instr :=
  [.load .d .r19 .r23 oOut, .load .d .r12 .r23 oN, .load .d .r6 .r23 oNLen, .addi .r21 .r23 0,
    .addi .r11 .r6 7, .lsr .d .r11 .r11 3, .lsl .r4 .r11 3, .addi .r4 .r4 16, .addi .r10 .r21 hdrBytes,
    .add .r5 .r10 .r4, .add .r8 .r5 .r4, .add .r9 .r8 .r4, .lsl .r11 .r11 1]

/-- `n`'s `2 w` words in `pre` `&=` the mask, `w = ⌈k / 8⌉`; the result
`r26 & 1` into `r3`. -/
def maskN : Prog isa :=
  .seq (.block [.load .d .r14 .r23 oOut, .load .d .r17 .r23 oNLen, .addi .r17 .r17 7, .lsr .d .r17 .r17 3,
      .lsl .r17 .r17 1])
    (.seq (Precompute.countLoop .r17 [.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r14 0,
        .addi .r14 .r14 8])
      (.block [.li .r3 1, .logic .and .r3 .r3 .r26]))

/-- `vg_rsa_private_precompute`. -/
def code : Prog isa :=
  .seq (.block (save ++ args)) (.seq zeroIn (.seq (.block setupX) (.seq Crt.loadX (.seq Crt.checks
  (.seq (.block ([.load .d .r30 .r23 oOut, .load .d .r3 .r23 oNLen, .addi .r3 .r3 7, .lsr .d .r3 .r3 3,
      .lsl .r3 .r3 4, .add .r30 .r30 .r3] ++ setupP oBP oPLen)) (.seq (prime 4)
  (.seq (.block (setupP oBQ oQLen)) (.seq (prime 5)
  (.seq (.block setupN) (.seq Precompute.core (.seq maskN (.block restore))))))))))))

end VG.Impl.Bignum.PPC64LE.PrivPre
