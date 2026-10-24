module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModExp
public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModArith

/-!
# The RSA private-key operation on PPC64LE

`vg_rsa_private_crt(out = r3, out_len = r4, n = r5, n_len = r6, input = r7,
input_len = r8, p = r9, p_len = r10, q, q_len, dp, dp_len, dq, dq_len, qinv,
qinv_len, scratch, scratch_len)`, the last ten on the stack: RSADP with the
key `(p, q, dP, dQ, qInv)` of the modulus `n`, `k = n_len` bytes.

Three working spaces in `scratch`, laid out as the public-key operation's
(`PublicChecked`), each with its header and eight arrays: `X` at `scratch`,
of `W = 2 ⌈k / 8⌉` words, then `P` and `Q` of `max(2, ⌈len / 8⌉)` words for
`p` and `q`.

* In `X`, with the modulus `M = 2^(64 W) - 1` in array 0: `n` (array 1),
  `p` (4), `q` (5), the input (6) and `qInv` (7) are loaded; the input below
  `n`, `qInv` below `p` and `n` valid give a mask (`r26`). With `M`,
  `R = 2^(64 W) ≡ 1`, so Montgomery multiplication (`MontMul.tail`, with
  `-M⁻¹ mod 2³² = 1`) computes `p q mod M = p q` exactly, compared with `n`
  both ways by `subMod`. Under a clear mask `p` and `q` become 3 and `qInv`
  0, so that the arithmetic below is the same whatever the key.
* In `P` (and `Q`): the prime, `c mod p` (`ModArith.reduce` over the input's
  bytes), `R² mod p` (`Precompute.r2`), `-p⁻¹ mod 2³²`, then
  `m₁ = c^dP mod p` (`ModExp.powSecret` over `dP`'s bytes).
* `h = (m₁ - m₂ mod p) qInv mod p`: `m₂`'s bytes into `X` array 1, reduced
  modulo `p`, subtracted with `subMod` and `p` added back under its borrow
  mask (`addMask`), then two Montgomery multiplications (by `qInv`, then by
  `R² mod p`).
* In `X`: `q h` exactly (Montgomery multiplication modulo `M`), plus `m₂`
  (`addMask` with an all-ones mask), written to `out` most significant first
  under the mask (`PublicChecked.output`), which returns 1 or 0.

Nothing branches on the input or the key's values: the loops count lengths.

The header holds the arguments (words 0–13) and the nonvolatile registers
(from byte 112). Registers kept: `r23` the working space, `r26` the mask,
`r27` `X`'s array 0, `r28` `X`'s arrays' size, `r21` the current working
space's array 0 (as `r10`, which some steps move).
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE.Crt

open VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE

/-- The header's words. -/
def oOut : Nat := 0
def oN : Nat := 8
def oNLen : Nat := 16
def oIn : Nat := 24
def oP : Nat := 32
def oPLen : Nat := 40
def oQ : Nat := 48
def oQLen : Nat := 56
def oDP : Nat := 64
def oDQ : Nat := 72
def oQInv : Nat := 80
def oBP : Nat := 96
def oBQ : Nat := 104

/-- The nonvolatile registers saved, `r23` (the working space) last. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31,
    .r23].getD i .r14

/-- Where register `i` is saved. -/
def savOff (i : Nat) : Nat := 112 + 8 * i

/-- The working space's address, the ninth argument on the stack, into
`r11`; the registers saved there, and its address into `r23`. -/
def save : List Instr :=
  [.addSp .r11 160, .load .d .r11 .r11 0] ++
    (List.range 18).flatMap (fun i => [.store .d (saved i) .r11 (savOff i)]) ++ [.addi .r23 .r11 0]

/-- The registers back, through `r23`, which is restored last. -/
def restore : List Instr :=
  (List.range 17).flatMap (fun i => [.load .d (saved i) .r23 (savOff i)]) ++
    [.load .d .r23 .r23 (savOff 17)]

/-- The arguments into the header. -/
def args : List Instr :=
  [.store .d .r3 .r23 oOut, .store .d .r5 .r23 oN, .store .d .r6 .r23 oNLen, .store .d .r7 .r23 oIn,
    .store .d .r9 .r23 oP, .store .d .r10 .r23 oPLen, .addSp .r11 96,
    .load .d .r0 .r11 0, .store .d .r0 .r23 oQ, .load .d .r0 .r11 8, .store .d .r0 .r23 oQLen,
    .load .d .r0 .r11 16, .store .d .r0 .r23 oDP, .load .d .r0 .r11 32, .store .d .r0 .r23 oDQ,
    .load .d .r0 .r11 48, .store .d .r0 .r23 oQInv]

/-- `rd := ⌈rs / 8⌉`, at least 2 (`rs` at least 1): `(rs + 7) / 8`, plus 1
if that is 1. -/
def words (rd rs : Reg) : List Instr :=
  [.addi rd rs 7, .lsr .d rd rd 3, .subi .r0 rd 2, .lsr .d .r0 .r0 63, .add rd rd .r0]

/-- The registers of a working space at `rb` of `w` words (in `r4`): array 0
in `r10` and `r21`, an array's size in `r29`, `2 w` in `r11`. -/
def area (rb : Reg) : List Instr :=
  [.addi .r10 rb hdrBytes, .addi .r21 .r10 0, .lsl .r29 .r4 3, .addi .r29 .r29 16, .lsl .r11 .r4 1]

/-- `X`: `W = 2 ⌈k / 8⌉` into `r4`, its registers, `r27` and `r28`, and the
bases of `P` and `Q` into the header. -/
def setupX : List Instr :=
  [.addi .r4 .r6 7, .lsr .d .r4 .r4 3, .lsl .r4 .r4 1] ++ area .r23 ++
    [.addi .r27 .r10 0, .addi .r28 .r29 0, .lsl .r5 .r29 3, .add .r5 .r10 .r5, .store .d .r5 .r23 oBP,
      .load .d .r3 .r23 oPLen] ++ words .r4 .r3 ++
    [.lsl .r3 .r4 3, .addi .r3 .r3 16, .lsl .r3 .r3 3, .addi .r3 .r3 hdrBytes, .add .r5 .r5 .r3,
      .store .d .r5 .r23 oBQ]

/-- `rd :=` the base of `X`'s array `j`. -/
def xb (rd : Reg) (j : Nat) : List Instr :=
  .addi rd .r27 0 :: List.replicate j (.add rd rd .r28)

/-- The `r11 / 2` words at `r14` := all ones. -/
def onesWords : Prog isa :=
  .seq (.block [.lsr .d .r17 .r11 1, .li .r0 0, .li .r3 1, .sub .r0 .r0 .r3])
    (Precompute.countLoop .r17 [.store .d .r0 .r14 0, .addi .r14 .r14 8])

/-- `k` bytes (`r6`) at `r12` into array `j`, as `Precompute.loadN` loads
`n` into array 0, and the array's word `w` := 0; `r10` restored. -/
def loadArr (j : Nat) : Prog isa :=
  .seq (.block (PublicChecked.base .r10 j)) (.seq Precompute.loadN
    (.block [.add .r14 .r10 .r29, .subi .r14 .r14 16, .li .r0 0, .store .d .r0 .r14 0, .addi .r10 .r21 0]))

/-- `X`'s arrays: `M`, `n`, `p`, `q`, the input and `qInv`. -/
def loadX : Prog isa :=
  .seq (.block [.addi .r14 .r10 0]) (.seq onesWords
    (.seq (.block [.load .d .r12 .r23 oN, .load .d .r6 .r23 oNLen]) (.seq (loadArr 1)
    (.seq (.block [.load .d .r12 .r23 oP, .load .d .r6 .r23 oPLen]) (.seq (loadArr 4)
    (.seq (.block [.load .d .r12 .r23 oQ, .load .d .r6 .r23 oQLen]) (.seq (loadArr 5)
    (.seq (.block [.load .d .r12 .r23 oIn, .load .d .r6 .r23 oNLen]) (.seq (loadArr 6)
    (.seq (.block [.load .d .r12 .r23 oQInv, .load .d .r6 .r23 oPLen]) (loadArr 7)))))))))))

/-- `r26 :=` all ones if `n` is valid (`Precompute.check`: `r0 = 0`), else 0. -/
def checkN : Prog isa :=
  .seq (.block [.load .d .r12 .r23 oN, .load .d .r6 .r23 oNLen]) (.seq Precompute.check
    (.block [.li .r3 1, .sub .r26 .r0 .r3]))

/-- `r26 &=` all ones if array `a` is below array `m`: `subMod` into array 3. -/
def checkLt (a m : Nat) : Prog isa :=
  .seq (.block (PublicChecked.base .r8 a ++ PublicChecked.base .r9 3 ++ PublicChecked.base .r10 m))
    (.seq subMod (.block [.logic .and .r26 .r26 .r20, .addi .r10 .r21 0]))

/-- `p q` into array 6 (Montgomery multiplication modulo `M`, `-M⁻¹ = 1`),
its word `W` := 0; then `r26 &=` all ones if it equals `n` (array 1): neither
is below the other. -/
def checkPQ : Prog isa :=
  .seq (.block [.li .r12 1]) (.seq (PublicChecked.montOp 6 4 5)
    (.seq (.block (PublicChecked.base .r14 6 ++ [.add .r14 .r14 .r29, .subi .r14 .r14 16, .li .r0 0,
        .store .d .r0 .r14 0] ++ PublicChecked.base .r8 6 ++ PublicChecked.base .r9 3 ++
        PublicChecked.base .r10 1))
      (.seq subMod (.seq (.block ([.addi .r24 .r20 0, .addi .r10 .r21 0] ++ PublicChecked.base .r8 1 ++
          PublicChecked.base .r9 3 ++ PublicChecked.base .r10 6))
        (.seq subMod (.block [.logic .or .r0 .r24 .r20, .li .r3 0, .subi .r3 .r3 1,
          .logic .xor .r0 .r0 .r3, .logic .and .r26 .r26 .r0, .addi .r10 .r21 0]))))))

/-- The `r11 / 2` words at `r14` `&= r26`. -/
def maskWords : Prog isa :=
  .seq (.block [.lsr .d .r17 .r11 1])
    (Precompute.countLoop .r17 [.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r14 0,
      .addi .r14 .r14 8])

/-- Array `j` := itself under the mask, else 3. -/
def orThree (j : Nat) : Prog isa :=
  .seq (.block (PublicChecked.base .r14 j)) (.seq maskWords
    (.block (PublicChecked.base .r14 j ++ [.load .d .r0 .r14 0, .li .r3 0, .subi .r3 .r3 1,
      .logic .xor .r3 .r3 .r26, .li .r4 3, .logic .and .r3 .r3 .r4, .logic .or .r0 .r0 .r3,
      .store .d .r0 .r14 0])))

/-- `X`'s checks into `r26`, and `p`, `q`, `qInv` masked. -/
def checks : Prog isa :=
  .seq checkN (.seq (checkLt 6 1) (.seq (checkLt 7 4) (.seq checkPQ
    (.seq (orThree 4) (.seq (orThree 5) (.seq (.block (PublicChecked.base .r14 7)) maskWords))))))

/-- `w` words (`r11 / 2`) from `r15` to `r14`. -/
def copyN : Prog isa := Precompute.copyWords

/-- A prime's working space at the header's word `oB`, of `max(2, ⌈len /
8⌉)` words for the length at `oLen`: its registers. -/
def setupP (oB oLen : Nat) : List Instr :=
  [.load .d .r3 .r23 oLen] ++ words .r4 .r3 ++ [.load .d .r3 .r23 oB] ++ area .r3

/-- In a prime's working space, the prime from `X`'s array `xj`, `c mod p` in
array 4, `R² mod p` in array 1, `-p⁻¹ mod 2³²` in `r12`, then
`c^d mod p` in array 4 for `d` at `oD` of the prime's length at `oLen`. -/
def power (xj oD oLen : Nat) : Prog isa :=
  .seq (.block ([.addi .r14 .r10 0] ++ xb .r15 xj)) (.seq copyN
  (.seq (.block [.load .d .r30 .r23 oIn, .load .d .r31 .r23 oNLen]) (.seq ModArith.reduce
  (.seq (.block (PublicChecked.base .r14 4 ++ PublicChecked.base .r15 1)) (.seq copyN
  (.seq (.block (PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3))
  (.seq Precompute.r2 (.seq (.block PublicChecked.minv)
  (.seq (.block [.load .d .r30 .r23 oD, .load .d .r31 .r23 oLen]) ModExp.powSecret)))))))))

/-- `m₂`'s `q_len` bytes, most significant first, from `Q`'s array 4 into
`X`'s array 1. -/
def exportM2 : Prog isa :=
  .seq (.block (PublicChecked.base .r15 4 ++ [.load .d .r17 .r23 oQLen, .add .r15 .r15 .r17,
      .subi .r15 .r15 1] ++ xb .r16 1))
    (Precompute.countLoop .r17 [.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1, .subi .r15 .r15 1])

/-- The array at `r15` `+= (r16's array) & r20` over `r11` digits, the carry
out dropped. -/
def addMask : Prog isa :=
  .seq (.block [.addi .r17 .r11 0, .li .r24 0])
    (Precompute.countLoop .r17 [.load .w .r0 .r15 0, .load .w .r3 .r16 0, .logic .and .r3 .r3 .r20,
      .add .r0 .r0 .r3, .add .r0 .r0 .r24, .store .w .r0 .r15 0, .lsr .d .r24 .r0 32, .addi .r15 .r15 4,
      .addi .r16 .r16 4])

/-- In `P`: `h = (m₁ - m₂ mod p) qInv mod p` into array 4, from `m₁` in array
4. -/
def recombineP : Prog isa :=
  -- `-p⁻¹ mod 2³²`; `R² mod p` (which `powSecret` overwrote) into array 7; `m₂ mod p` into array 1.
  .seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++
      PublicChecked.base .r9 3)) (.seq Precompute.r2
  (.seq (.block (PublicChecked.base .r14 7 ++ PublicChecked.base .r15 1)) (.seq copyN
  (.seq (.block (xb .r30 1 ++ [.load .d .r31 .r23 oQLen])) (.seq ModArith.reduce
  -- `m₁ - m₂ mod p` into array 3, `p` added back under the borrow.
  (.seq (.block (PublicChecked.base .r14 4 ++ [.add .r14 .r14 .r29, .subi .r14 .r14 16, .li .r0 0,
      .store .d .r0 .r14 0] ++ PublicChecked.base .r8 4 ++ PublicChecked.base .r9 3 ++
      PublicChecked.base .r10 1))
  (.seq subMod (.seq (.block ([.addi .r10 .r21 0] ++ PublicChecked.base .r15 3 ++
      PublicChecked.base .r16 0)) (.seq addMask
  -- `qInv` into array 6; `h` into array 4.
  (.seq (.block (PublicChecked.base .r14 6 ++ xb .r15 7)) (.seq copyN
  (.seq (PublicChecked.montOp 5 3 6) (PublicChecked.montOp 4 5 7)))))))))))))

/-- In `X`: `m = q h + m₂` into array 4, from `h` in `P`'s array 4 and `m₂`
in `Q`'s. -/
def recombineX : Prog isa :=
  -- `h` into array 7, `m₂` into array 6, zero-extended.
  .seq (.block (setupP oBP oPLen ++ PublicChecked.base .r15 4 ++ [.addi .r22 .r11 0, .lsl .r11 .r4 1] ++
      xb .r14 7 ++ [.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2]))
  (.seq Precompute.zeroWords (.seq (.block (xb .r14 7 ++ [.addi .r11 .r22 0])) (.seq copyN
  (.seq (.block (setupP oBQ oQLen ++ PublicChecked.base .r15 4 ++ [.addi .r22 .r11 0] ++
      xb .r14 6 ++ [.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2]))
  (.seq Precompute.zeroWords (.seq (.block (xb .r14 6 ++ [.addi .r11 .r22 0])) (.seq copyN
  -- `q h` modulo `M`, exactly; `+ m₂`.
  (.seq (.block [.addi .r10 .r27 0, .addi .r21 .r27 0, .addi .r29 .r28 0, .addi .r11 .r28 0,
      .subi .r11 .r11 16, .lsr .d .r11 .r11 2, .li .r12 1])
  (.seq (PublicChecked.montOp 4 5 7) (.seq (.block (xb .r15 4 ++ xb .r16 6 ++ [.li .r20 0,
      .subi .r20 .r20 1])) addMask))))))))))

/-- `vg_rsa_private_crt`. -/
def crt : Prog isa :=
  .seq (.block (save ++ args ++ setupX)) (.seq loadX (.seq checks
  (.seq (.block (setupP oBP oPLen)) (.seq (power 4 oDP oPLen)
  (.seq (.block (setupP oBQ oQLen)) (.seq (power 5 oDQ oQLen) (.seq exportM2
  (.seq (.block (setupP oBP oPLen)) (.seq recombineP (.seq recombineX
  (.seq (.block [.addi .r10 .r27 0, .addi .r29 .r28 0, .load .d .r27 .r23 oOut, .load .d .r28 .r23 oNLen])
    (.seq PublicChecked.output (.block restore)))))))))))))

end VG.Impl.Bignum.PPC64LE.Crt
