module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common

/-!
# DSA verification on PPC64LE

`vg_dsa_verify(key = r3, key_len = r4, p_len = r5, q_len = r6,
signature = r7, signature_len = r8, digest = r9, digest_len = r10,
scratch, scratch_len)`, `scratch` and `scratch_len` on the stack. After
`checkKey` (`Common.lean`), which branches on the public key only:

* in the Q space, the mask of `0 < r < q` and `0 < s < q` (`subMod`'s
  borrow and `eqMask` with 0), `R² mod q` (into array 8 too), `q − 2`
  (two `subMod`s of 1) to the buffer, `w = s^(q − 2) mod q` (`powSecret` over its
  octets), then `u1 = z w mod q` and `u2 = r w mod q` (two Montgomery
  multiplications each, by w and by R²), for the digest's scalar `z` (its
  first `min(digest_len, bitLength q / 8)` octets), to the buffer;
* in the P space, `g^u1 mod p` (kept in array 9) and `y^u2 mod p`, and their
  product `v` to the buffer;
* in the Q space, `v mod q` (`reduce`) compared with r (`eqMask`).

The result is that comparison under the mask: nothing branches on the
signature or the digest, only on their lengths and on the key.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp minv one)
open VG.Impl.MillerRabin.PPC64LE (eqMask copy)

/-- `min(digest_len, 64)` into `r4`, without a branch: `r10` unless
`r10 >> 6` is not zero. -/
def capD : List Instr :=
  [.lsr .d .r4 .r10 6, .li .r0 0, .sub .r4 .r0 .r4, .lsr .d .r4 .r4 63, .sub .r4 .r0 .r4, .li .r0 64,
    .logic .xor .r0 .r10 .r0, .logic .and .r0 .r0 .r4, .logic .xor .r4 .r10 .r0]

/-- The working space from the stack, the registers saved there, the key,
the signature and the digest into `r27`, `r28` and `r26`, and the lengths into
`r2`. -/
def entry : List Instr :=
  [.addSp .r11 96, .load .d .r11 .r11 0] ++ save .r11 ++
    [.addi .r27 .r3 0, .addi .r28 .r7 0, .addi .r26 .r9 0] ++ capD ++
    [.lsl .r4 .r4 48, .lsl .r0 .r6 16, .add .r2 .r5 .r0, .add .r2 .r2 .r4]

/-- r's octets: the signature, `q_len`. -/
def ptrR : List Instr := [.addi .r12 .r28 0] ++ getQ .r6

/-- s's octets: the signature plus `q_len`, `q_len`. -/
def ptrS : List Instr := ptrR ++ [.add .r12 .r12 .r6]

/-- The buffer, `q_len` octets. -/
def ptrBuf : List Instr := bufBase .r12 .r0 ++ getQ .r6

/-- The buffer from `q_len` on, `q_len` octets. -/
def ptrBuf2 : List Instr := ptrBuf ++ [.add .r12 .r12 .r6]

/-- 0 into array `j`. -/
def zeroArr (j : Nat) : Prog isa := .seq (.block (base .r14 j)) Precompute.zeroWords

/-- `r22 &=` the mask of `0 < [a] < q`, with 0 in array 7. -/
def inRange (a : Nat) : Prog isa :=
  .seq (.block (base .r8 a ++ base .r9 3)) (.seq subMod (.seq (eqMask .r19 a 7)
    (.block (clear19 ++ [.logic .and .r22 .r22 .r20]))))

/-- In the Q space: q in array 0; r into array 5 and s into array 6, and
`r22 :=` the mask of both in range. -/
def ranges : Prog isa :=
  .seq (.block (enterQ ++ ptrR)) (.seq (loadArr 5) (.seq (.block ptrS) (.seq (loadArr 6)
    (.seq (zeroArr 7) (.seq (.block [.li .r22 0, .subi .r22 .r22 1]) (.seq (inRange 5) (inRange 6)))))))

/-- The mask into the header's word `hMask` (secret: it stays in memory). -/
def keepMask : List Instr := [.store .d .r22 .r21 hMask]

/-- `R² mod q` into array 1 and array 8. -/
def rrQ : Prog isa :=
  .seq (.block (base .r5 1 ++ base .r8 2 ++ base .r9 3)) (.seq Precompute.r2 (copy 8 1))

/-- `q − 2` to the buffer: 1 into array 7, `[4] := [0] − [7]` and `[6] := [4] − [7]`
(`subMod`). -/
def qMinus2 : Prog isa :=
  .seq one (.seq (.block (base .r8 0 ++ base .r9 4 ++ base .r10 7)) (.seq subMod
    (.seq (.block ([.addi .r10 .r31 hdrBytes] ++ base .r8 4 ++ base .r9 6 ++ base .r10 7)) (.seq subMod
      (.seq (.block ([.addi .r10 .r31 hdrBytes] ++ ptrBuf)) (storeBE 6))))))

/-- `w = s^(q − 2) mod q` into array 4: s again into array 4, `R² mod q` into
array 1, the power over the buffer's `q_len` octets. -/
def inverse : Prog isa :=
  .seq (.block ptrS) (.seq (loadArr 4) (.seq (copy 1 8)
    (.seq (.block (ptrBuf ++ [.addi .r30 .r12 0, .addi .r31 .r6 0] ++ minv)) (.seq ModExp.powSecret
      (.block [.addi .r31 .r23 0])))))

/-- `r6 := min(digest_len, qb)`: `min(digest_len, 64)` unless above `qb`
(both at most 64). -/
def scalarLen : Prog isa :=
  .seq (.block (getQb .r6 ++ getD .r0 ++ [.sub .r3 .r6 .r0, .lsr .d .r3 .r3 63]))
    (.ite (.zero .d .r3) (.block [.logic .or .r6 .r0 .r0]) (.block []))

/-- The digest's scalar into array 6: its first `min(digest_len, qb)`
octets, or 0 if there are none. -/
def scalar : Prog isa :=
  .seq scalarLen (.seq (.block [.addi .r12 .r26 0]) (.ite (.zero .d .r6) (zeroArr 6) (loadArr 6)))

/-- `u1 = z w mod q` into array 6 and `u2 = r w mod q` into array 5, then both
to the buffer. -/
def products : Prog isa :=
  .seq scalar (.seq (.block ptrR) (.seq (loadArr 5) (.seq (copy 1 8) (.seq (.block minv)
    (.seq (montOp 6 6 4) (.seq (montOp 6 6 1) (.seq (montOp 5 5 4) (.seq (montOp 5 5 1)
      (.seq (.block ptrBuf) (.seq (storeBE 6) (.seq (.block ptrBuf2) (storeBE 5))))))))))))

/-- In the P space, the power of the number at `r12` (`p_len` octets) by the
`q_len` octets at `r24`, into array 4. -/
def powP : Prog isa :=
  .seq (.block (getP .r6)) (.seq (loadArr 4) (.seq (copy 1 8)
    (.seq (.block ([.addi .r30 .r24 0] ++ getQ .r31 ++ minv)) (.seq ModExp.powSecret
      (.block [.addi .r31 .r23 0])))))

/-- `v = g^u1 y^u2 mod p` into array 7, then to the buffer (`p_len` octets). -/
def combine : Prog isa :=
  .seq (.block (enterP ++ ptrG ++ bufBase .r24 .r0)) (.seq powP (.seq (copy 9 4)
    (.seq (.block (ptrBuf2 ++ [.addi .r24 .r12 0] ++ ptrY)) (.seq powP (.seq (copy 1 8)
      (.seq (.block minv) (.seq (montOp 5 4 1) (.seq (copy 6 9) (.seq (montOp 7 6 5)
        (.seq (.block (bufBase .r12 .r0 ++ getP .r6)) (storeBE 7)))))))))))

/-- In the Q space, `v mod q` (`reduce` of the buffer's `p_len` octets) into
array 1, r into array 5, and `r3 :=` 1 if they are equal and the mask in
`hMask` is all ones, else 0. -/
def compare : Prog isa :=
  .seq (.block (enterQ ++ bufBase .r30 .r0 ++ getP .r31)) (.seq ModArith.reduce
    (.seq (.block ([.addi .r31 .r23 0] ++ ptrR)) (.seq (loadArr 5) (.seq (eqMask .r3 1 5)
      (.block [.load .d .r4 .r21 hMask, .logic .and .r3 .r3 .r4, .li .r0 1, .logic .and .r3 .r3 .r0])))))

/-- The verification, after the check of the key. -/
def body : Prog isa :=
  .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products (.seq combine compare))))))

/-- `vg_dsa_verify`. -/
def verify : Prog isa :=
  .seq (.block entry) (.seq (checkKey body (.block [.li .r3 0])) (.block restore))

end VG.Impl.Dsa.PPC64LE.Verify
