module

public import VerifiedGarbage.Impl.Bignum.RISCV64.ModExp
public import VerifiedGarbage.Impl.Bignum.RISCV64.ModArith
public import VerifiedGarbage.Impl.Bignum.CrtLayout

/-!
# The RSA private-key operation on RISC-V

`vg_rsa_private_crt(out = a0, out_len = a1, n = a2, n_len = a3, input = a4,
input_len = a5, p = a6, p_len = a7, q, q_len, dp, dp_len, dq, dq_len, qinv,
qinv_len, scratch, scratch_len)`, the last ten on the stack (`sp`, `sp + 8`,
…): RSADP with the key `(p, q, dP, dQ, qInv)` of the modulus `n`, `k = n_len`
bytes, as on PPC64LE (`Impl/Bignum/PPC64LE/Crt.lean`), on words of 64 bits.

Three working spaces in `scratch`, laid out as the public-key operation's
(`PublicChecked`), each with its header: `X` at `scratch`, with eight arrays
of `W = 2 ⌈k / 8⌉` words, then `P` and `Q`, with 24 arrays (for the windows'
table, `ModExp.powWin`) of `max(2, ⌈len / 8⌉)` words for `p` and `q`.

* In `X`, with the modulus `M = 2^(64 W) - 1` in array 0: `n` (array 1),
  `p` (4), `q` (5), the input (6) and `qInv` (7) are loaded; the input below
  `n`, `qInv` below `p` and `n` valid give a mask (`s9`, then the header's
  `oMask`). With `M`, `R = 2^(64 W) ≡ 1`, so Montgomery multiplication
  (`MontMul.tail`, with `-M⁻¹ mod 2⁶⁴ = 1`) computes `p q mod M = p q`
  exactly, compared with `n` both ways by `subMod64`. Under a clear mask `p`
  and `q` become 3 and `qInv` 0, so that the arithmetic below is the same
  whatever the key.
* The input into `X`'s array 6 again (`loadIn`).
* In `P` (and `Q`): the prime, `-p⁻¹ mod 2⁶⁴` (`Precompute.minv`), `R² mod
  p` (`r2Prime`: `64 w + w` doublings from 1, then six squares by `sqrTail`),
  `c mod p` (`reduceIn`: Montgomery multiplications, a chunk of `c`'s words at
  a time), then `m₁ = c^dP mod p` (`ModExp.powWin`).
* `h = (m₁ - m₂ mod p) qInv mod p`: `m₂` into `X`'s array 6, zero-extended
  (`widen`); in `P`, `m₁` moved to array 9, `m₂ mod p` by `reduceIn` (with
  the `R² mod p` that `power` left in array 1), subtracted with `subMod64` and
  `p` added back under its borrow mask (`ModArith.addMask64`), then two
  Montgomery multiplications (by `qInv`, then by `R² mod p`).
* In `X`: `q h` exactly (Montgomery multiplication modulo `M`), plus `m₂`
  (`addMask64` with an all-ones mask), written to `out` most significant first
  under the mask (`PublicChecked.output`), which returns 1 or 0.

Nothing branches on the input or the key's values: the loops count lengths.

The header holds the arguments and the mask (words 0–13) and the
callee-saved registers and `ra` (from byte 112). Registers kept: `s6` the
working space, `s11` `X`'s arrays' size, `ra` the current working space's
array 0 (as `a7`, which some steps move), `s5` its arrays' size, `t0` its
`w`; `s9` the mask in `X`; in a prime's working space, `s7`–`s10` the scans'
registers (`ModArith`, `ModExp`).
-/

@[expose] public section

namespace VG.Impl.Bignum.RISCV64.Crt

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp output)

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
def oMask : Nat := 88
def oBP : Nat := 96
def oBQ : Nat := 104

/-- The callee-saved registers and `ra` saved, `s6` (the working space)
last. -/
def saved (i : Nat) : Reg :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s7, .s8, .s9, .s10, .s11, .ra, .s6].getD i .s0

/-- Where register `i` is saved. -/
def savOff (i : Nat) : Nat := 112 + 8 * i

/-- The working space's address, the ninth stack argument, into `t0`; the
registers saved there, and its address into `s6`. -/
def save : List Instr :=
  [.addSp .t0 64, .load .d .t0 .t0 0] ++
    (List.range 13).flatMap (fun i => [.store .d (saved i) .t0 (savOff i)]) ++ [.addi .s6 .t0 0]

/-- The registers back, through `s6`, which is restored last. -/
def restore : List Instr :=
  (List.range 12).flatMap (fun i => [.load .d (saved i) .s6 (savOff i)]) ++
    [.load .d .s6 .s6 (savOff 12)]

/-- The arguments into the header. -/
def args : List Instr :=
  [.store .d .a0 .s6 oOut, .store .d .a2 .s6 oN, .store .d .a3 .s6 oNLen, .store .d .a4 .s6 oIn,
    .store .d .a6 .s6 oP, .store .d .a7 .s6 oPLen, .addSp .t2 0,
    .load .d .t3 .t2 0, .store .d .t3 .s6 oQ, .load .d .t3 .t2 8, .store .d .t3 .s6 oQLen,
    .load .d .t3 .t2 16, .store .d .t3 .s6 oDP, .load .d .t3 .t2 32, .store .d .t3 .s6 oDQ,
    .load .d .t3 .t2 48, .store .d .t3 .s6 oQInv]

/-- `rd := ⌈rs / 8⌉`, at least 2 (`rs` at least 1): `(rs + 7) / 8`, plus 1
if that is 1. -/
def words (rd rs : Reg) : List Instr :=
  [.addi rd rs 7, .shift .srl .d rd rd 3, .addi .t3 rd (-2), .shift .srl .d .t3 .t3 63, .add rd rd .t3]

/-- The registers of a working space at `rb` of `w` words (in `t2`): array 0
in `a7` and `ra`, an array's size in `s5`, `w` in `t0`. -/
def area (rb : Reg) : List Instr :=
  [.addi .a7 rb hdrBytes, .addi .ra .a7 0, .shift .sll .d .s5 .t2 3, .addi .s5 .s5 16, .addi .t0 .t2 0]

/-- `X`: `W = 2 ⌈k / 8⌉` (from `k` in `a3`), its registers and `s11`, and the
bases of `P` and `Q` into the header. -/
def setupX : List Instr :=
  [.addi .t2 .a3 7, .shift .srl .d .t2 .t2 3, .shift .sll .d .t2 .t2 1] ++ area .s6 ++
    [.addi .s11 .s5 0, .shift .sll .d .t4 .s5 3, .add .t4 .a7 .t4, .store .d .t4 .s6 oBP,
      .load .d .t3 .s6 oPLen] ++ words .t2 .t3 ++
    [.shift .sll .d .t3 .t2 3, .addi .t3 .t3 16, .shift .sll .d .t3 .t3 3, .add .t5 .t3 .t3, .add .t3 .t3 .t5,
      .addi .t3 .t3 hdrBytes, .add .t4 .t4 .t3, .store .d .t4 .s6 oBQ]

/-- `rd :=` the base of `X`'s array `j`. -/
def xb (rd : Reg) (j : Nat) : List Instr :=
  .addi rd .s6 hdrBytes :: List.replicate j (.add rd rd .s11)

/-- The `w` words at `t3` := all ones. -/
def onesWords : Prog isa :=
  .seq (.block [.addi .t5 .t0 0, .li .s0 (-1)])
    (countLoop .t5 [.store .d .s0 .t3 0, .addi .t3 .t3 8])

/-- `k` bytes (`s8`) at `s7` into array `j`, as `Precompute.loadN` loads `n`
into array 0, and the array's word `w` := 0; `a7` restored. -/
def loadArr (j : Nat) : Prog isa :=
  .seq (.block (base .a7 j)) (.seq Precompute.loadN
    (.block [.add .t3 .a7 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0, .addi .a7 .ra 0]))

/-- `X`'s arrays: `M`, `n`, `p`, `q`, the input and `qInv`. -/
def loadX : Prog isa :=
  .seq (.block [.addi .t3 .a7 0]) (.seq onesWords
    (.seq (.block [.load .d .s7 .s6 oN, .load .d .s8 .s6 oNLen]) (.seq (loadArr 1)
    (.seq (.block [.load .d .s7 .s6 oP, .load .d .s8 .s6 oPLen]) (.seq (loadArr 4)
    (.seq (.block [.load .d .s7 .s6 oQ, .load .d .s8 .s6 oQLen]) (.seq (loadArr 5)
    (.seq (.block [.load .d .s7 .s6 oIn, .load .d .s8 .s6 oNLen]) (.seq (loadArr 6)
    (.seq (.block [.load .d .s7 .s6 oQInv, .load .d .s8 .s6 oPLen]) (loadArr 7)))))))))))

/-- `s9 :=` all ones if `n` is valid (`Precompute.check`: `s0 = 0`), else 0:
`s0 = 0` exactly when `(s0 >> 1 | s0 & 1) - 1` has its top bit set. -/
def checkN : Prog isa :=
  .seq (.block [.load .d .s7 .s6 oN, .load .d .s8 .s6 oNLen]) (.seq Precompute.check
    (.block [.shift .srl .d .t2 .s0 1, .logicImm .and .t3 .s0 1, .logic .or .t2 .t2 .t3, .addi .t2 .t2 (-1),
      .shift .srl .d .t2 .t2 63, .li .t3 0, .sub .s9 .t3 .t2]))

/-- `s4 :=` all ones if array `a` is below array `m`, else 0: `subMod64` into
array 3; `a7` back to array 0. -/
def cmpLt (a m : Nat) : Prog isa :=
  .seq (.block (base .a5 a ++ base .a6 3 ++ base .a7 m)) (.seq subMod64 (.block [.addi .a7 .ra 0]))

/-- `s9 &=` all ones if array `a` is below array `m`. -/
def checkLt (a m : Nat) : Prog isa :=
  .seq (cmpLt a m) (.block [.logic .and .s9 .s9 .s4])

/-- `p q` into array 6 (Montgomery multiplication modulo `M`, `-M⁻¹ = 1`),
its word `W` := 0; then `s9 &=` all ones if it equals `n` (array 1): neither
is below the other. -/
def checkPQ : Prog isa :=
  .seq (.block [.li .t1 1]) (.seq (montOp 6 4 5)
    (.seq (.block (base .t3 6 ++ [.add .t3 .t3 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0]))
      (.seq (cmpLt 6 1) (.seq (.block [.addi .s7 .s4 0]) (.seq (cmpLt 1 6)
        (.block [.logic .or .t2 .s7 .s4, .logicImm .xor .t2 .t2 (-1), .logic .and .s9 .s9 .t2]))))))

/-- The `w` words at `t3` `&= s9`. -/
def maskWords : Prog isa :=
  .seq (.block [.addi .t5 .t0 0])
    (countLoop .t5 [.load .d .s0 .t3 0, .logic .and .s0 .s0 .s9, .store .d .s0 .t3 0, .addi .t3 .t3 8])

/-- Array `j` := itself under the mask, else 3. -/
def orThree (j : Nat) : Prog isa :=
  .seq (.block (base .t3 j)) (.seq maskWords
    (.block (base .t3 j ++ [.load .d .s0 .t3 0, .logicImm .xor .t2 .s9 (-1), .logicImm .and .t2 .t2 3,
      .logic .or .s0 .s0 .t2, .store .d .s0 .t3 0])))

/-- `X`'s checks into `s9`, `p`, `q`, `qInv` masked, and the mask into the
header. -/
def checks : Prog isa :=
  .seq checkN (.seq (checkLt 6 1) (.seq (checkLt 7 4) (.seq checkPQ
    (.seq (orThree 4) (.seq (orThree 5) (.seq (.block (base .t3 7)) (.seq maskWords
      (.block [.store .d .s9 .s6 oMask]))))))))

/-- `w` words from `t4` to `t3`. -/
def copyN : Prog isa := Precompute.copyWords

/-- A prime's working space at the header's word `oB`, of `max(2, ⌈len /
8⌉)` words for the length at `oLen`: its registers. -/
def setupP (oB oLen : Nat) : List Instr :=
  [.load .d .t3 .s6 oLen] ++ words .t2 .t3 ++ [.load .d .t4 .s6 oB] ++ area .t4

/-- `x := R² mod m = 2^(128 w) mod m` in array 1 (`a2`), for any odd `m` of
`w` words in array 0, with `-m⁻¹ mod 2⁶⁴` in `t1` and the bases of arrays 2
and 3 in `a5` and `a6`: `x := 1`; `64 w + w` doublings to `2^w R mod m`
(`Precompute.doubleMod64`, counted by `a1`); then six Montgomery squares
(`sqrTail`, with array `tmp` its temporary) to `2^(64 w) R mod m`, counted by
`s7`, as PPC64LE's `Precompute.r2Prime`. -/
def r2Prime (tmp : Nat) : Prog isa :=
  .seq (.block [.addi .t3 .a2 0]) (.seq Precompute.zeroWords
  (.seq (.block [.li .s0 1, .store .d .s0 .a2 0, .shift .sll .d .a1 .t0 6, .add .a1 .a1 .t0])
  (.seq (.loop (.seq Precompute.doubleMod64 (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1))
  (.seq (.block [.li .s7 6])
    (.loop (.seq (ModExp.sqrOp 1 1 tmp) (.block [.addi .s7 .s7 (-1)])) (.nonzero .s7))))))

/-- The input into `X`'s array 6 (`checks` used it for `p q`), for the
reductions modulo the primes. -/
def loadIn : Prog isa := .seq (.block [.load .d .s7 .s6 oIn, .load .d .s8 .s6 oNLen]) (loadArr 6)

/-- One chunk of `reduceIn`: the next `w` words of `c` (at `s9`) into array 6;
`T := C q R⁻¹ mod p` into array 7 and `q := q R² R⁻¹ mod p`; `S := S - T mod
p` (into array 3, `p` added back under the borrow, then back into array 4);
`s10 -= w`, and `t2 :=` 1 if any words remain (`s10 > 0`), else 0. -/
def chunkStep : Prog isa :=
  .seq (.block (base .t3 6 ++ [.addi .t4 .s9 0])) (.seq copyN
  (.seq (.block [.addi .s9 .t4 0]) (.seq (montOp 7 6 5) (.seq (montOp 5 5 1)
  (.seq (.block (base .t3 4 ++ [.add .t3 .t3 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0] ++
      base .a5 4 ++ base .a6 3 ++ base .a7 7))
  (.seq subMod64 (.seq (.block ([.addi .a7 .ra 0] ++ base .t3 3 ++ base .t4 0))
  (.seq ModArith.addMask64 (.seq (.block (base .t3 4 ++ base .t4 3)) (.seq copyN
  (.block [.sub .s10 .s10 .t0, .addi .t2 .s10 (-1), .shift .srl .d .t2 .t2 63, .logicImm .xor .t2 .t2 1])))))))))))

/-- `c mod p` into array 4, for `c` in `X`'s array 6 (`⌈k / 8⌉` words of
`R = 2^(64 w)`), `p` in array 0, `R² mod p` in array 1 and `-p⁻¹ mod 2⁶⁴` in
`t1`: `p - 1` into array 8 (`p` is odd), `q := (p - 1) R² R⁻¹ = -R mod p`
into array 5, `S := 0` in array 4, then `chunkStep` for each chunk `C_i` of
`w` words from the bottom, which keeps `q ≡ -R^(i+1)` and adds `C_i R^i ≡
-C_i q R⁻¹` to `S`. -/
def reduceIn : Prog isa :=
  .seq (.block (base .t3 8 ++ [.addi .t4 .a7 0])) (.seq copyN
  (.seq (.block (base .t3 8 ++ [.load .d .s0 .t3 0, .addi .s0 .s0 (-1), .store .d .s0 .t3 0]))
  (.seq (montOp 5 1 8) (.seq (.block (base .t3 4)) (.seq Precompute.zeroWords
  (.seq (.block (xb .s9 6 ++ [.load .d .s10 .s6 oNLen, .addi .s10 .s10 7, .shift .srl .d .s10 .s10 3]))
    (.loop chunkStep (.nonzero .t2))))))))

/-- In a prime's working space, the prime from `X`'s array `xj`, `-p⁻¹ mod
2⁶⁴` in `t1`, `R² mod p` in array 1 (`r2Prime`), `c mod p` in array 4
(`reduceIn`), then `c^d mod p` in array 4 for `d` at `oD` of the prime's
length at `oLen` (`ModExp.powWin`, with its table in arrays 8 to 23). -/
def power (xj oD oLen : Nat) : Prog isa :=
  .seq (.block ([.addi .t3 .a7 0] ++ xb .t4 xj)) (.seq copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3))
  (.seq (r2Prime 4) (.seq reduceIn
  (.seq (.block [.load .d .s9 .s6 oD, .load .d .s10 .s6 oLen]) ModExp.powWin)))))

/-- In `P`: `h = (m₁ - m₂ mod p) qInv mod p` into array 4, from `m₁` in array
4, `R² mod p` in array 1 (left by `power`) and `m₂` in `X`'s array 6. -/
def recombineP : Prog isa :=
  -- `m₁` into array 9; `-p⁻¹ mod 2⁶⁴`; `m₂ mod p` into array 4 (`reduceIn`).
  .seq (.block (base .t3 9 ++ base .t4 4)) (.seq copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3)) (.seq reduceIn
  -- `m₁ - m₂ mod p` into array 3, `p` added back under the borrow.
  (.seq (.block (base .t3 9 ++ [.add .t3 .t3 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0] ++
      base .a5 9 ++ base .a6 3 ++ base .a7 4))
  (.seq subMod64 (.seq (.block ([.addi .a7 .ra 0] ++ base .t3 3 ++ base .t4 0)) (.seq ModArith.addMask64
  -- `qInv` into array 6; `h` into array 4.
  (.seq (.block (base .t3 6 ++ xb .t4 7)) (.seq copyN
  (.seq (montOp 5 3 6) (montOp 4 5 1)))))))))))

/-- `t0 := W`, `X`'s words, from its arrays' size `s11 = 8 W + 16`. -/
def wX : List Instr := [.addi .t0 .s11 (-16), .shift .srl .d .t0 .t0 3]

/-- `X`'s array `xj` := the prime working space's array 4 (`w` words, at
`oB`, of the length at `oLen`), zero-extended to `W` words. -/
def widen (oB oLen xj : Nat) : Prog isa :=
  .seq (.block (setupP oB oLen ++ base .s9 4 ++ [.addi .s8 .t0 0] ++ xb .t3 xj ++ wX))
    (.seq Precompute.zeroWords (.seq (.block (xb .t3 xj ++ [.addi .t4 .s9 0, .addi .t0 .s8 0])) copyN))

/-- In `X`: `m = q h + m₂` into array 4, from `h` in `P`'s array 4 and `m₂`
in `Q`'s. -/
def recombineX : Prog isa :=
  -- `h` into array 7, `m₂` into array 6, zero-extended.
  .seq (widen oBP oPLen 7) (.seq (widen oBQ oQLen 6)
  -- `q h` modulo `M`, exactly; `+ m₂`.
  (.seq (.block ([.addi .a7 .s6 hdrBytes, .addi .ra .a7 0, .addi .s5 .s11 0] ++ wX ++ [.li .t1 1]))
  (.seq (montOp 4 5 7) (.seq (.block (xb .t3 4 ++ xb .t4 6 ++ [.li .s4 (-1)])) ModArith.addMask64))))

/-- `vg_rsa_private_crt`. -/
def crt : Prog isa :=
  .seq (.block (save ++ args ++ setupX)) (.seq loadX (.seq checks (.seq loadIn
  (.seq (.block (setupP oBP oPLen)) (.seq (power 4 oDP oPLen)
  (.seq (.block (setupP oBQ oQLen)) (.seq (power 5 oDQ oQLen) (.seq (widen oBQ oQLen 6)
  (.seq (.block (setupP oBP oPLen)) (.seq recombineP (.seq recombineX
  (.seq (.block [.addi .a7 .s6 hdrBytes, .addi .s5 .s11 0, .load .d .s10 .s6 oOut, .load .d .s11 .s6 oNLen,
      .load .d .s9 .s6 oMask])
    (.seq output (.block restore))))))))))))))

end VG.Impl.Bignum.RISCV64.Crt
