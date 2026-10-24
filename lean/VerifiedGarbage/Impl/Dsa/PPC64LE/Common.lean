module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModExp
public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModArith
public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Round

/-!
# DSA on PPC64LE: the working spaces and the check of the public key

The DSA functions work in `scratch` (at least `16 p_len` words), at `S`, in
two working spaces of the public-key operation's layout
(`Impl/Bignum/PPC64LE/PublicChecked.lean`: a header of 32 words, then arrays
of `w + 2` words), and a buffer:

* the P space at `S`, of `w = p_len / 8` words and 28 arrays, for arithmetic
  modulo p;
* the Q space after it (at `S + slot w 28`), of `w = 4` words (q has at most
  32 octets) and 28 arrays, for arithmetic modulo q;
* the buffer after that, of `2 p_len` octets: `ModExp.powSecret` and
  `ModArith.reduce` read their numbers as octets in memory, most significant
  first, so a number moves from one space to the other through it
  (`storeBE`, `loadArr`).

The arithmetic is `Impl/Bignum/PPC64LE`'s and the Miller–Rabin round's
(`eqMask`, `copy`): with array 0 (the modulus) at `r10`, the arrays' size in
`r29`, `2 w` in `r11`, the space in `r23` and `r31`, and `-m⁻¹ mod 2³²` in
`r12` (`PublicChecked.minv`, again after every load, which uses `r12`).

The addresses and the lengths stay in registers that no arithmetic writes
(`r21`, `r2`, `r26`–`r28`), so they are public throughout; the P space's
header keeps the nonvolatile registers in its words 13–31.

`checkKey` checks the public part of the key, `parametersValid`
(`checkParams`, which also checks a domain alone) and `y`'s part of
`keyValid`, on public values only, and branches on them:

* the sizes: `bitLength p` and `bitLength q` are the sizes of a supported
  pair, all multiples of 8, so each is 8 times the number's significant
  octets exactly when its first significant octet has its top bit set
  (`sigLen`, `topBit`); then q < p follows, and 1 < q;
* p and q are odd (their last octets);
* `(p − 1) mod q = 0`, as `p mod q = 1` (`ModArith.reduce` in the Q space);
* `1 < g < p` and `g^q mod p = 1`, then the same of y (`checkElem`, with
  `ModExp.powSecret` over q's octets in the P space, R² mod p kept in
  array 8).
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.MillerRabin.PPC64LE (eqMask copy)

/-! ## The values kept in registers

`r21` keeps `S`; `r2` the lengths, `p_len | q_len << 16 | qb << 32 | d << 48`
(`qb` q's significant octets, set by `sizes`, and `d = min(digest_len, 64)`);
`r27` the key, `r28` the signature (or the nonce), `r26` the digest. No
arithmetic writes them, so the addresses and the lengths are public
throughout. -/

/-- `rd := p_len`. -/
def getP (rd : Reg) : List Instr := [.lsl rd .r2 48, .lsr .d rd rd 48]

/-- `rd := q_len`. -/
def getQ (rd : Reg) : List Instr := [.lsl rd .r2 32, .lsr .d rd rd 48]

/-- `rd :=` q's significant octets. -/
def getQb (rd : Reg) : List Instr := [.lsl rd .r2 16, .lsr .d rd rd 48]

/-- `rd := min(digest_len, 64)`. -/
def getD (rd : Reg) : List Instr := [.lsr .d rd .r2 48]

/-- The header's word that keeps verification's mask of r's and s's ranges. -/
def hMask : Nat := 0

/-! ## Saving the nonvolatile registers -/

/-- The nonvolatile registers saved, `r21` (which keeps `S`) last. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31,
    .r2, .r21].getD i .r14

/-- The byte offset of saved register `i` in the header. -/
def saveOff (i : Nat) : Nat := 104 + 8 * i

/-- Save them in the P space at `ws`, and keep its address in `r21`. -/
def save (ws : Reg) : List Instr :=
  (List.range 19).flatMap (fun i => [.store .d (saved i) ws (saveOff i)]) ++ [.addi .r21 ws 0]

/-- Restore them, through `r21`, which is restored last. -/
def restore : List Instr :=
  (List.range 18).flatMap (fun i => [.load .d (saved i) .r21 (saveOff i)]) ++ [.load .d .r21 .r21 (saveOff 18)]

/-! ## The working spaces -/

/-- `rd :=` the Q space, `S + 704 + 28 p_len` (`slot (p_len / 8) 28` on), through `t`. -/
def qBase (rd t : Reg) : List Instr := getP rd ++ [.li t 28, .mul rd rd t, .addi rd rd 704, .add rd rd .r21]

/-- `rd :=` the buffer, 1600 octets past the Q space, through `t`. -/
def bufBase (rd t : Reg) : List Instr := qBase rd t ++ [.addi rd rd 1600]

/-- Into the P space: `w = p_len / 8`. -/
def enterP : List Instr :=
  [.addi .r23 .r21 0, .addi .r31 .r21 0, .addi .r10 .r21 hdrBytes] ++ getP .r11 ++
    [.lsr .d .r11 .r11 3, .lsl .r29 .r11 3, .addi .r29 .r29 16, .lsl .r11 .r11 1]

/-- Into the Q space: `w = 4`. -/
def enterQ : List Instr :=
  qBase .r23 .r11 ++ [.addi .r31 .r23 0, .addi .r10 .r23 hdrBytes, .li .r11 8, .li .r29 48]

/-- The `k = r6` octets at `r12`, most significant first, into array `j`, and
the array's word `w` := 0 (as `subMod` reads it); then `r10` back to array 0. -/
def loadArr (j : Nat) : Prog isa :=
  .seq (.block (base .r10 j)) (.seq Precompute.loadN
    (.block [.add .r14 .r10 .r29, .subi .r14 .r14 16, .li .r0 0, .store .d .r0 .r14 0,
      .addi .r10 .r31 hdrBytes]))

/-- Array `j`'s low `k = r6` octets, most significant first, to `r12`. -/
def storeBE (j : Nat) : Prog isa :=
  .seq (.block (base .r15 j ++ [.add .r15 .r15 .r6, .subi .r15 .r15 1, .addi .r16 .r12 0, .addi .r17 .r6 0]))
    (Precompute.countLoop .r17 [.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1, .subi .r15 .r15 1])

/-! ## The sizes -/

/-- `r16 :=` the significant octets of the `k = r6` octets at `r12` (from the
first that is not zero): `r15` or's the octets so far, and each octet from
the first nonzero one adds 1. -/
def sigLen : Prog isa :=
  .seq (.block [.addi .r14 .r12 0, .addi .r17 .r6 0, .li .r15 0, .li .r16 0])
    (Precompute.countLoop .r17 [.lbz .r0 .r14 0, .logic .or .r15 .r15 .r0, .li .r3 0, .sub .r3 .r3 .r15,
      .lsr .d .r3 .r3 63, .add .r16 .r16 .r3, .addi .r14 .r14 1])

/-- `r0 := 0` exactly when the first significant octet (`r16 ≠ 0` of them)
has its top bit set. -/
def topBit : List Instr :=
  [.add .r14 .r12 .r6, .sub .r14 .r14 .r16, .lbz .r0 .r14 0, .lsr .d .r0 .r0 7, .li .r3 1,
    .logic .xor .r0 .r0 .r3]

/-- `r0 := 0` exactly when the number at `r12` (`r6` octets) has a bit length
of 8 times its `r16` significant octets, which is not zero. -/
def bytesBits : Prog isa :=
  .seq sigLen (.ite (.zero .d .r16) (.block [.li .r0 1]) (.block topBit))

/-- `r0 := 0` if the significant octets `(r24, r25)` are `(P, Q)`. -/
def pairOk (P Q : Nat) : Prog isa :=
  .seq (.block [.subi .r3 .r24 P, .subi .r4 .r25 Q, .logic .or .r3 .r3 .r4])
    (.ite (.zero .d .r3) (.block [.li .r0 0]) (.block []))

/-- `r0 := 0` exactly when `(8 r24, 8 r25)` are supported sizes of p and q. -/
def pairs : Prog isa :=
  .seq (.block [.li .r0 1]) (.seq (pairOk 128 20) (.seq (pairOk 256 20) (.seq (pairOk 256 28)
    (.seq (pairOk 256 32) (pairOk 384 32)))))

/-- `r0 := 0` exactly when the last of the `r6` octets at `r12` is odd. -/
def odd : List Instr :=
  [.add .r14 .r12 .r6, .subi .r14 .r14 1, .lbz .r0 .r14 0, .li .r3 1, .logic .and .r0 .r0 .r3,
    .logic .xor .r0 .r0 .r3]

/-- `c`, then `rest` if `r0 = 0`, else `fail`. -/
def andThen (c rest fail : Prog isa) : Prog isa := .seq c (.ite (.zero .d .r0) rest fail)

/-- p's octets: the key, `p_len`. -/
def ptrP : List Instr := [.addi .r12 .r27 0] ++ getP .r6

/-- q's octets: the key plus `p_len`, `q_len`. -/
def ptrQ : List Instr := getP .r0 ++ [.add .r12 .r27 .r0] ++ getQ .r6

/-- g's octets: the key plus `p_len + q_len`, `p_len`. -/
def ptrG : List Instr := getP .r6 ++ getQ .r0 ++ [.add .r12 .r27 .r6, .add .r12 .r12 .r0]

/-- y's octets: the key plus `2 p_len + q_len`, `p_len`. -/
def ptrY : List Instr := ptrG ++ [.add .r12 .r12 .r6]

/-- The sizes: p's significant octets into `r24`, q's into `r25` and `r2`'s
`qb`, each with its top bit set, and a supported pair. -/
def sizes (rest fail : Prog isa) : Prog isa :=
  andThen (.seq (.block ptrP) bytesBits)
    (.seq (.block [.addi .r24 .r16 0]) (andThen (.seq (.block ptrQ) bytesBits)
      (.seq (.block [.addi .r25 .r16 0, .lsl .r0 .r16 32, .add .r2 .r2 .r0]) (andThen pairs rest fail))
      fail)) fail

/-- p and q odd. -/
def odds (rest fail : Prog isa) : Prog isa :=
  andThen (.block (ptrP ++ odd)) (andThen (.block (ptrQ ++ odd)) rest fail) fail

/-- `r0 := 0` exactly when the masks `r3` is all ones (else 0). -/
def unmask : List Instr := [.li .r4 1, .logic .and .r3 .r3 .r4, .logic .xor .r0 .r3 .r4]

/-- In the Q space: q into array 0, then `r0 := 0` exactly when `p mod q = 1`
(`reduce` into array 1, compared with 1 in array 7). -/
def pModQ : Prog isa :=
  .seq (.block enterQ) (.seq (.seq (.block ptrQ) (loadArr 0))
    (.seq (.block ([.addi .r30 .r27 0] ++ getP .r31)) (.seq ModArith.reduce
      (.seq (.block [.addi .r31 .r23 0]) (.seq PublicChecked.one (.seq (eqMask .r3 1 7) (.block unmask)))))))

/-- In the P space: p into array 0, `R² mod p` into array 8 (and array 1). -/
def setupP : Prog isa :=
  .seq (.block enterP) (.seq (.seq (.block ptrP) (loadArr 0))
    (.seq (.block (base .r5 1 ++ base .r8 2 ++ base .r9 3)) (.seq Precompute.r2 (copy 8 1))))

/-- `r20 &= ¬r19`. -/
def clear19 : List Instr := [.logic .or .r20 .r20 .r19, .logic .xor .r20 .r20 .r19]

/-- In the P space, with p in array 0: `r0 := 0` exactly when array 4 is
above 1 and below p (`subMod`'s borrow, `eqMask` with 0 in array 5 and 1 in
array 7). -/
def elemRange : Prog isa :=
  .seq PublicChecked.one (.seq (.block ([.addi .r10 .r31 hdrBytes] ++ base .r14 5)) (.seq Precompute.zeroWords
    (.seq (.block (base .r8 4 ++ base .r9 3)) (.seq subMod (.seq (eqMask .r19 4 5) (.seq (.block clear19)
      (.seq (eqMask .r19 4 7) (.block (clear19 ++ [.addi .r3 .r20 0] ++ unmask)))))))))

/-- In the P space, with p in array 0 and `R² mod p` in array 8: `r0 := 0`
exactly when array 4's q-th power modulo p is 1 (`powSecret` over q's
octets, compared with 1 in array 7). -/
def elemOrder : Prog isa :=
  .seq (copy 1 8) (.seq (.block (ptrQ ++ [.addi .r30 .r12 0, .addi .r31 .r6 0] ++ PublicChecked.minv))
    (.seq ModExp.powSecret (.seq (.block [.addi .r31 .r23 0]) (.seq PublicChecked.one
      (.seq (eqMask .r3 4 7) (.block unmask))))))

/-- The number at `r12` (`p_len` octets, in `r6`) into array 4, then `r0 := 0`
exactly when it is above 1, below p, and its q-th power modulo p is 1. -/
def checkElem : Prog isa := .seq (loadArr 4) (andThen elemRange elemOrder (.block []))

/-- The check of the domain p||q||g at `r27`: sizes, oddness, `p mod q = 1`
and g; then `rest`, or `fail`. In the P space after it, with p in array 0 and
`R² mod p` in array 8. -/
def checkParams (rest fail : Prog isa) : Prog isa :=
  sizes (odds (andThen pModQ (.seq setupP (andThen (.seq (.block ptrG) checkElem) rest fail)) fail) fail) fail

/-- The check of the key's public part: the domain's (`checkParams`), then y;
then `rest`, or `fail`. In the P space after it, with p in array 0 and
`R² mod p` in array 8. -/
def checkKey (rest fail : Prog isa) : Prog isa :=
  checkParams (andThen (.seq (.block ptrY) checkElem) rest fail) fail

end VG.Impl.Dsa.PPC64LE
