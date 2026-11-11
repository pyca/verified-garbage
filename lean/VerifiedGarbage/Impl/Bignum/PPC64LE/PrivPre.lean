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
* `n`'s values, as `vg_rsa_public_precompute` computes them
  (`Precompute.core`, in the working space laid out for `w` words at `X`'s
  base, which leaves `X`'s arrays 4 and 5 as they are), which are zeros if
  `n` is not valid; `R² mod n` from them into `X`'s array 6, zero-extended to
  its `2 w` words (`xIn`).
* For each factor, in its working space (`Crt.setupP`): the factor, its
  `-p⁻¹ mod 2³²` and `R² mod p` from `R² mod n` (`r2Fast`), written to `pre`
  after `n`'s values, under the mask.
* `n`'s values in `pre` and-ed with the mask, and the result `r26 & 1`.

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

/-! ## `R_p² mod p` from `R² mod n`

`vg_rsa_private_crt` computes `R_p² mod p` by `65 w_p` doublings of 1
(`Precompute.r2Prime`). Here `x = R² mod n` is known (`X`'s array 6, from
`Precompute.core`), and for `p | n`, `x ≡ 2^(128 w)` modulo `p`. Steps of
Montgomery reduction (`chunkStep1`, `S := S R_p⁻¹ - C_i R_p⁻¹`, over `x`'s
`K = ⌈w / w_p⌉` chunks `C_i` of `w_p` words, zero-extended; then
`S := S R_p⁻¹` while more than `2 w_p` of `x`'s `2 w` words are left,
`zStep`) give `-S ≡ x R_p^(-K - Z) = 2^(64 e)` for the `e` words left,
`1 ≤ e ≤ 2 w_p` (`Proof/Bignum/PrimeR2.lean`). Then doublings to
`2^(128 w_p)`, or, if `e ≤ w_p`, to `2^(64 w_p + w_p)` and six Montgomery
squares (`r2Fast`). For factors of half `n`'s words, `e = 2 w_p`: two
steps and nothing else. Every count is of the lengths: `w` from `X`'s
array size (`r28 = 16 (w + 1)`), `w_p` from `r11 = 2 w_p`. -/

/-- `S := S - T mod p`, for `S` in array 4 and `T` in array 7: into array 3,
`p` added back under the borrow (as `Crt.chunkStep`'s), then back into array
4. -/
def subST : Prog isa :=
  .seq (.block (PublicChecked.base .r14 4 ++ [.add .r14 .r14 .r29, .subi .r14 .r14 16, .li .r0 0,
      .store .d .r0 .r14 0] ++ PublicChecked.base .r8 4 ++ PublicChecked.base .r9 3 ++ PublicChecked.base .r10 7))
  (.seq subMod (.seq (.block ([.addi .r10 .r21 0] ++ PublicChecked.base .r15 3 ++ PublicChecked.base .r16 0))
  (.seq addMask (.seq (.block (PublicChecked.base .r14 4 ++ PublicChecked.base .r15 3)) copyN))))

/-- One step of the reduction: the next `w_p` words of `x` (at `r25`) into
array 6, `T := C 1 R⁻¹` into array 7 and `S := S 1 R⁻¹` (1 in array 1),
`S := S - T mod p` (`subST`); `r31 -= w_p`, and `r3 :=` 1 if `r31 > 0`,
else 0. -/
def chunkStep1 : Prog isa :=
  .seq (.block (PublicChecked.base .r14 6 ++ [.addi .r15 .r25 0])) (.seq copyN
  (.seq (.block [.addi .r25 .r15 0]) (.seq (PublicChecked.montOp 7 6 1) (.seq (PublicChecked.montOp 4 4 1)
  (.seq subST
  (.block [.lsr .d .r3 .r11 1, .sub .r31 .r31 .r3, .subi .r3 .r31 1, .lsr .d .r3 .r3 63, .li .r0 1,
    .logic .xor .r3 .r3 .r0]))))))

/-- A further reduction: `S := S 1 R⁻¹`; `e := e - w_p` (`r31`), and `r3 :=`
1 if `e > 2 w_p`, else 0. -/
def zStep : Prog isa :=
  .seq (PublicChecked.montOp 4 4 1)
    (.block [.lsr .d .r3 .r11 1, .sub .r31 .r31 .r3, .sub .r3 .r11 .r31, .lsr .d .r3 .r3 63])

/-- `S := -S mod p`: `S` into array 7, array 4 := 0, then `subST`. -/
def negS : Prog isa :=
  .seq (.block (PublicChecked.base .r14 7 ++ PublicChecked.base .r15 4)) (.seq copyN
  (.seq (.block (PublicChecked.base .r14 4)) (.seq Precompute.zeroWords subST)))

/-- `r4` doublings of array 1 modulo `p`. -/
def dblLoop : Prog isa :=
  .loop (.seq Precompute.doubleMod64 (.block [.subi .r4 .r4 1])) (.nonzero .d .r4)

/-- `R² mod p` into array 1, for `p` in array 0, `-p⁻¹ mod 2³²` in `r12` and
the bases of arrays 1–3 in `r5`, `r8` and `r9`, from `x = R² mod n` in
`X`'s array 6 (`2 w` words, `x` zero-extended): 1 into array 1, `S := 0` in
array 4, the reduction's `K` steps from `r31 = w` while `r31 > 0`
(`chunkStep1`, the chunks at `r25`), then from `e = r31 + w` the further
ones while `e > 2 w_p` (`zStep`), `-S` (`negS`) into array 1, and the
doublings and squares. -/
def r2Fast : Prog isa :=
  .seq Precompute.one (.seq (.block (PublicChecked.base .r14 4)) (.seq Precompute.zeroWords
  (.seq (.block (xb .r25 6 ++ [.lsr .d .r31 .r28 4, .subi .r31 .r31 1]))
  (.seq (.loop chunkStep1 (.nonzero .d .r3))
  (.seq (.block [.lsr .d .r3 .r28 4, .subi .r3 .r3 1, .add .r31 .r31 .r3, .sub .r3 .r11 .r31, .lsr .d .r3 .r3 63])
  (.seq (.ite (.nonzero .d .r3) (.loop zStep (.nonzero .d .r3)) (.block []))
  (.seq negS
  (.seq (.block (PublicChecked.base .r14 1 ++ PublicChecked.base .r15 4)) (.seq copyN
  (.seq (.block (PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3 ++
      [.lsr .d .r4 .r11 1, .sub .r3 .r4 .r31, .lsr .d .r3 .r3 63]))
    (.ite (.nonzero .d .r3)
      (.seq (.block [.sub .r4 .r11 .r31, .lsl .r4 .r4 6]) (.ite (.nonzero .d .r4) dblLoop (.block [])))
      (.seq (.block [.lsr .d .r4 .r11 1, .sub .r3 .r4 .r31, .lsl .r3 .r3 6, .add .r4 .r3 .r4]) (.seq dblLoop
        (.seq (.block [.li .r24 6])
          (.loop (.seq Precompute.r2Sq (.block [.subi .r24 .r24 1])) (.nonzero .d .r24))))))))))))))))

/-- In a factor's working space, the factor from `X`'s array `xj`, its
`-p⁻¹ mod 2³²` in `r12` and `R² mod p` in array 1 (`r2Fast`); then its `w_p` words (`r11 / 2`), and-ed with the mask, to `pre` at
`r30`, which is advanced past them. -/
def prime (xj : Nat) : Prog isa :=
  .seq (.block ([.addi .r14 .r10 0] ++ xb .r15 xj)) (.seq copyN
  (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++
      PublicChecked.base .r9 3))
  (.seq r2Fast
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

/-- `R² mod n`, `pre`'s words `w` to `2 w` (`r19`), into `X`'s array 6,
zero-extended to its `2 w` words, for `r11 = 2 w`. -/
def xIn : Prog isa :=
  .seq (.block (xb .r14 6 ++ [.lsl .r11 .r11 1])) (.seq Precompute.zeroWords
    (.seq (.block ([.lsr .d .r11 .r11 1] ++ xb .r14 6 ++ [.lsl .r3 .r11 2, .add .r15 .r19 .r3]))
      Precompute.copyWords))

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
  (.seq (.block setupN) (.seq Precompute.core (.seq xIn
  (.seq (.block ([.load .d .r30 .r23 oOut, .load .d .r3 .r23 oNLen, .addi .r3 .r3 7, .lsr .d .r3 .r3 3,
      .lsl .r3 .r3 4, .add .r30 .r30 .r3] ++ setupP oBP oPLen)) (.seq (prime 4)
  (.seq (.block (setupP oBQ oQLen)) (.seq (prime 5)
  (.seq maskN (.block restore)))))))))))))

end VG.Impl.Bignum.PPC64LE.PrivPre
