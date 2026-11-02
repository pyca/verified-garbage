module

public import VerifiedGarbage.Impl.Bignum.RISCV64.ModExp
public import VerifiedGarbage.Impl.Bignum.RISCV64.ModArith

/-!
# DSA on RISC-V: the working spaces and the check of the public key

As on PPC64LE (`Impl/Dsa/PPC64LE/Common.lean`), the DSA functions work in
`scratch` (at least `16 p_len` words), at `S`, in two working spaces of the
public-key operation's layout (`Impl/Bignum/Layout.lean`: a header of 32
words, then arrays of `w + 2` words), and a buffer:

* the P space at `S`, of `w = p_len / 8` words and 28 arrays, for arithmetic
  modulo p;
* the Q space after it (at `S + slot (p_len / 8) 28`), of `w = ⌈q_len / 8⌉`
  words and 28 arrays (`1600` bytes at most), for arithmetic modulo q;
* the buffer after that, of `2 p_len` octets: `ModExp.powWin` and
  `ModArith.reduce64` read their numbers as octets in memory, most
  significant first, so a number moves from one space to the other through
  it (`storeBE`, `loadArr`).

The arithmetic is `Impl/Bignum/RISCV64`'s, in its registers (`a7` array 0's
base, `s5` an array's size, `t0` `w`, `t1` `-m⁻¹ mod 2⁶⁴`). `powWin` uses
arrays 0–23, of which it writes 1–23, so the values kept across a power are
in arrays 24–27: `R² mod m` in array 24.

Unlike PPC64LE's, the modulus's top word may be zero: a valid domain's p may
have fewer significant octets than `p_len`, and q than `q_len`. So `R² mod m`
is `2^(128 w) mod m` by `128 w` doublings of 1 (`rr`, by `MontMul.lean`'s
`doubleMod64`), which needs only `m` odd and at least 2, rather than
`Precompute.r2`, which needs the top word set; and an array's word `w` is set
to 0 before a number is loaded into it (`loadArr`), so that the comparison
of `subMod64`, which reads it, sees the whole number.

The addresses stay in registers that no arithmetic writes: `s6` keeps `S`,
`s11` the key and `ra` the signature (or the nonce), so they are public
throughout. The lengths, and the digest's address, are in the P space's
header (`hLens`, `hDigest`), which no arithmetic writes either; the
callee-saved registers and `ra` are saved there too, in words 16–28.

`checkKey` checks the public part of the key as PPC64LE's does, on public
values only, and branches on them: the sizes, p and q odd, `p mod q = 1`,
then `1 < g < p` and `g^q mod p = 1`, and the same of y (`checkElem`).
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-! ## The values kept

`s6` keeps `S`, `s11` the key, `ra` the signature (or the nonce); the
header's word `hLens` the lengths, `p_len | q_len << 16 | qb << 32 | d << 48`
(`qb` q's significant octets, set by `sizes`, and `d = min(digest_len, 64)`). -/

/-- The header's byte offset of verification's mask of r's and s's ranges. -/
def hMask : Nat := 0

/-- The header's byte offset of the digest's address. -/
def hDigest : Nat := 8

/-- The header's byte offset of the lengths. -/
def hLens : Nat := 16

/-- `rd := p_len`. -/
def getP (rd : Reg) : List Instr := [.load .d rd .s6 hLens, .shift .sll .d rd rd 48, .shift .srl .d rd rd 48]

/-- `rd := q_len`. -/
def getQ (rd : Reg) : List Instr := [.load .d rd .s6 hLens, .shift .sll .d rd rd 32, .shift .srl .d rd rd 48]

/-- `rd :=` q's significant octets. -/
def getQb (rd : Reg) : List Instr := [.load .d rd .s6 hLens, .shift .sll .d rd rd 16, .shift .srl .d rd rd 48]

/-- `rd := min(digest_len, 64)`. -/
def getD (rd : Reg) : List Instr := [.load .d rd .s6 hLens, .shift .srl .d rd rd 48]

/-! ## Saving the callee-saved registers -/

/-- The registers saved, `s6` (which keeps `S`) last. -/
def saved (i : Nat) : Reg :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s7, .s8, .s9, .s10, .s11, .ra, .s6].getD i .s0

/-- The byte offset of saved register `i` in the header: words 16–28. -/
def saveOff (i : Nat) : Nat := 128 + 8 * i

/-- Save them in the P space at `ws`, and keep its address in `s6`. -/
def save (ws : Reg) : List Instr :=
  (List.range 13).flatMap (fun i => [.store .d (saved i) ws (saveOff i)]) ++ [.addi .s6 ws 0]

/-- Restore them, through `s6`, which is restored last. -/
def restore : List Instr :=
  (List.range 12).flatMap (fun i => [.load .d (saved i) .s6 (saveOff i)]) ++ [.load .d .s6 .s6 (saveOff 12)]

/-! ## The working spaces -/

/-- `rd :=` the Q space, `S + 704 + 28 p_len` (`slot (p_len / 8) 28` on), through `t`. -/
def qBase (rd t : Reg) : List Instr :=
  getP rd ++ [.li t 28, .mul rd rd t, .addi rd rd 704, .add rd rd .s6]

/-- `rd :=` the buffer, 1600 octets past the Q space, through `t`. -/
def bufBase (rd t : Reg) : List Instr := qBase rd t ++ [.addi rd rd 1600]

/-- Into the P space: `w = p_len / 8`. -/
def enterP : List Instr :=
  [.addi .a7 .s6 hdrBytes] ++ getP .t0 ++
    [.shift .srl .d .t0 .t0 3, .shift .sll .d .s5 .t0 3, .addi .s5 .s5 16]

/-- Into the Q space: `w = ⌈q_len / 8⌉`. -/
def enterQ : List Instr :=
  qBase .a7 .t2 ++ [.addi .a7 .a7 hdrBytes] ++ getQ .t0 ++
    [.addi .t0 .t0 7, .shift .srl .d .t0 .t0 3, .shift .sll .d .s5 .t0 3, .addi .s5 .s5 16]

/-- `a7` back to array 0 from array `j`. -/
def back (j : Nat) : List Instr := List.replicate j (.sub .a7 .a7 .s5)

/-- The `k = s8` octets at `s7`, most significant first, into array `j`,
whose word `w` is set to 0 first; then `a7` back to array 0. -/
def loadArr (j : Nat) : Prog isa :=
  .seq (.block (List.replicate j (.add .a7 .a7 .s5) ++
      [.add .t3 .a7 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0]))
    (.seq Precompute.loadN (.block (back j)))

/-- Array `j`'s low `k = s8` octets, most significant first, to `s7`. -/
def storeBE (j : Nat) : Prog isa :=
  .seq (.block (base .t3 j ++ [.add .t3 .t3 .s8, .addi .t3 .t3 (-1), .addi .t4 .s7 0, .addi .t5 .s8 0]))
    (countLoop .t5 [.load .b .s0 .t3 0, .store .b .s0 .t4 0, .addi .t4 .t4 1, .addi .t3 .t3 (-1)])

/-- The `w` words of array `j` := 0. -/
def zeroArr (j : Nat) : Prog isa := .seq (.block (base .t3 j)) Precompute.zeroWords

/-- `rd :=` all ones if arrays `j` and `k` are equal in their `w` words, else
0: the or of the words' xors, compared with 0. -/
def eqMask (rd : Reg) (j k : Nat) : Prog isa :=
  .seq (.block (base .t3 j ++ base .t4 k ++ [.addi .t5 .t0 0, .li .t2 0]))
    (.seq (countLoop .t5 [.load .d .s0 .t3 0, .load .d .s1 .t4 0, .logic .xor .s0 .s0 .s1,
        .logic .or .t2 .t2 .s0, .addi .t3 .t3 8, .addi .t4 .t4 8])
      (.block [.li .s0 0, .sltu .s1 .s0 .t2, .addi rd .s1 (-1)]))

/-- `[o] := [a]` over the `w + 2` words of the arrays, for any arrays. -/
def copy (o a : Nat) : Prog isa :=
  .seq (.block (base .t3 o ++ base .t4 a ++ [.addi .t5 .t0 2]))
    (countLoop .t5 [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8])

/-- `R² mod m = 2^(128 w) mod m` into array 1 and array 24: 1 into array 1,
then `128 w` of `x := 2 x mod m` (`doubleMod64`, `x` in array 1), counted by
`a1`. -/
def rr : Prog isa :=
  .seq (.block (base .a2 1 ++ base .a5 2 ++ base .a6 3 ++ [.addi .t3 .a2 0])) (.seq Precompute.zeroWords
    (.seq (.block [.li .s0 1, .store .d .s0 .a2 0, .shift .sll .d .a1 .t0 7])
      (.seq (.loop (.seq Precompute.doubleMod64 (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1))
        (copy 24 1))))

/-! ## The sizes -/

/-- `a1 :=` the significant octets of the `k = s8` octets at `s7` (from the
first that is not zero): `t4` or's the octets so far, and each octet from
the first nonzero one adds 1. -/
def sigLen : Prog isa :=
  .seq (.block [.addi .t3 .s7 0, .addi .t5 .s8 0, .li .t4 0, .li .a1 0])
    (countLoop .t5 [.load .b .s0 .t3 0, .logic .or .t4 .t4 .s0, .li .a0 0, .sub .a0 .a0 .t4,
      .shift .srl .d .a0 .a0 63, .add .a1 .a1 .a0, .addi .t3 .t3 1])

/-- `a0 := 0` exactly when the first significant octet (`a1 ≠ 0` of them)
has its top bit set. -/
def topBit : List Instr :=
  [.add .t3 .s7 .s8, .sub .t3 .t3 .a1, .load .b .a0 .t3 0, .shift .srl .d .a0 .a0 7, .li .t4 1,
    .logic .xor .a0 .a0 .t4]

/-- `a0 := 0` exactly when the number at `s7` (`s8` octets) has a bit length
of 8 times its `a1` significant octets, which is not zero. -/
def bytesBits : Prog isa :=
  .seq sigLen (.ite (.zero .a1) (.block [.li .a0 1]) (.block topBit))

/-- `a0 := 0` if the significant octets `(a2, a3)` are `(P, Q)`. -/
def pairOk (P Q : Nat) : Prog isa :=
  .seq (.block [.addi .t3 .a2 (-(P : Int)), .addi .t4 .a3 (-(Q : Int)), .logic .or .t3 .t3 .t4])
    (.ite (.zero .t3) (.block [.li .a0 0]) (.block []))

/-- `a0 := 0` exactly when `(8 a2, 8 a3)` are supported sizes of p and q. -/
def pairs : Prog isa :=
  .seq (.block [.li .a0 1]) (.seq (pairOk 128 20) (.seq (pairOk 256 20) (.seq (pairOk 256 28)
    (.seq (pairOk 256 32) (pairOk 384 32)))))

/-- `a0 := 0` exactly when the last of the `s8` octets at `s7` is odd. -/
def odd : List Instr :=
  [.add .t3 .s7 .s8, .addi .t3 .t3 (-1), .load .b .a0 .t3 0, .logicImm .and .a0 .a0 1,
    .logicImm .xor .a0 .a0 1]

/-- `c`, then `rest` if `a0 = 0`, else `fail`. -/
def andThen (c rest fail : Prog isa) : Prog isa := .seq c (.ite (.zero .a0) rest fail)

/-- p's octets: the key, `p_len`. -/
def ptrP : List Instr := [.addi .s7 .s11 0] ++ getP .s8

/-- q's octets: the key plus `p_len`, `q_len`. -/
def ptrQ : List Instr := getP .t3 ++ [.add .s7 .s11 .t3] ++ getQ .s8

/-- g's octets: the key plus `p_len + q_len`, `p_len`. -/
def ptrG : List Instr := getP .s8 ++ getQ .t3 ++ [.add .s7 .s11 .s8, .add .s7 .s7 .t3]

/-- y's octets: the key plus `2 p_len + q_len`, `p_len`. -/
def ptrY : List Instr := ptrG ++ [.add .s7 .s7 .s8]

/-- The sizes: p's significant octets into `a2`, q's into `a3` and the
lengths' `qb`, each with its top bit set, and a supported pair. -/
def sizes (rest fail : Prog isa) : Prog isa :=
  andThen (.seq (.block ptrP) bytesBits)
    (.seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits)
      (.seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
          .store .d .t4 .s6 hLens]) (andThen pairs rest fail))
      fail)) fail

/-- p and q odd. -/
def odds (rest fail : Prog isa) : Prog isa :=
  andThen (.block (ptrP ++ odd)) (andThen (.block (ptrQ ++ odd)) rest fail) fail

/-- `a0 := 0` exactly when the mask `a0` is all ones (else 0). -/
def unmask : List Instr := [.logicImm .and .a0 .a0 1, .logicImm .xor .a0 .a0 1]

/-- Into the Q space, and q into its array 0. -/
def setupQ : Prog isa := .seq (.block enterQ) (.seq (.block ptrQ) (loadArr 0))

/-- In the Q space: q into array 0 (`setupQ`), then `a0 := 0` exactly when
`p mod q = 1` (`reduce64` into array 1, compared with 1 in array 7). -/
def pModQ : Prog isa :=
  .seq setupQ
    (.seq (.block ([.addi .s9 .s11 0] ++ getP .s10)) (.seq ModArith.reduce64
      (.seq PublicChecked.one (.seq (eqMask .a0 1 7) (.block unmask)))))

/-- In the P space: p into array 0, `-p⁻¹ mod 2⁶⁴` into `t1`, `R² mod p`
into arrays 1 and 24 (`rr`). -/
def setupP : Prog isa :=
  .seq (.block enterP) (.seq (.seq (.block ptrP) (loadArr 0)) (.seq (.block Precompute.minv) rr))

/-- `a1 &= ¬a2`. -/
def clear : List Instr := [.logic .or .a1 .a1 .a2, .logic .xor .a1 .a1 .a2]

/-- With m in array 0: `a1 :=` all ones if array `a` is below m, else 0
(`subMod64`'s borrow, array 3 its temporary). -/
def below (a : Nat) : Prog isa :=
  .seq (.block (base .a5 a ++ base .a6 3)) (.seq subMod64 (.block [.addi .a1 .s4 0]))

/-- In the P space, with p in array 0: `a0 := 0` exactly when array 4 is
above 1 and below p (`below`, `eqMask` with 0 in array 5 and 1 in array 7). -/
def elemRange : Prog isa :=
  .seq PublicChecked.one (.seq (zeroArr 5) (.seq (below 4) (.seq (eqMask .a2 4 5) (.seq (.block clear)
    (.seq (eqMask .a2 4 7) (.block (clear ++ [.addi .a0 .a1 0] ++ unmask)))))))

/-- In the P space, with p in array 0 and `R² mod p` in array 24: `a0 := 0`
exactly when array 4's q-th power modulo p is 1 (`powWin` over q's octets,
compared with 1 in array 7). -/
def elemOrder : Prog isa :=
  .seq (copy 1 24) (.seq (.block (ptrQ ++ [.addi .s9 .s7 0, .addi .s10 .s8 0]))
    (.seq ModExp.powWin (.seq PublicChecked.one (.seq (eqMask .a0 4 7) (.block unmask)))))

/-- The number at `s7` (`p_len` octets, in `s8`) into array 4, then `a0 := 0`
exactly when it is above 1, below p, and its q-th power modulo p is 1. -/
def checkElem : Prog isa := .seq (loadArr 4) (andThen elemRange elemOrder (.block []))

/-- The check of the domain p||q||g at `s11`: sizes, oddness, `p mod q = 1`
and g; then `rest`, or `fail`. In the P space after it, with p in array 0,
`-p⁻¹ mod 2⁶⁴` in `t1` and `R² mod p` in array 24. -/
def checkParams (rest fail : Prog isa) : Prog isa :=
  sizes (odds (andThen pModQ (.seq setupP (andThen (.seq (.block ptrG) checkElem) rest fail)) fail) fail) fail

/-- The check of the key's public part: the domain's (`checkParams`), then y;
then `rest`, or `fail`. In the P space after it, as `checkParams` leaves it. -/
def checkKey (rest fail : Prog isa) : Prog isa :=
  checkParams (andThen (.seq (.block ptrY) checkElem) rest fail) fail

end VG.Impl.Dsa.RISCV64
