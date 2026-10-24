module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common

/-!
# DSA verification on PPC64LE

`vg_dsa_verify(key = r3, key_len = r4, p_len = r5, q_len = r6,
signature = r7, signature_len = r8, digest = r9, digest_len = r10,
scratch, scratch_len)`, `scratch` and `scratch_len` on the stack. After
`checkKey` (`Common.lean`), which branches on the public key only:

* in the Q space, the mask `r26` of `0 < r < q` and `0 < s < q` (`subMod`'s
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

/-- The working space from the stack, the registers saved there, and the
arguments kept in the header: the key, `q_len`, the signature, the digest
and its length; then the layout from `p_len`. -/
def entry : List Instr :=
  [.addSp .r11 96, .load .d .r11 .r11 0] ++ save .r11 ++
    [.store .d .r3 .r21 hKey, .store .d .r6 .r21 hQ, .store .d .r7 .r21 hSig, .store .d .r9 .r21 hDig,
      .store .d .r10 .r21 hDlen, .addi .r6 .r5 0] ++ layout

/-- `hDlen := min(digest_len, q's significant octets)`: `digest_len` if it is
below 64 and below them, else them. -/
def digestLen : Prog isa :=
  .seq (.block [.load .d .r3 .r21 hDlen, .load .d .r4 .r21 hQb, .lsr .d .r0 .r3 6])
    (.ite (.zero .d .r0)
      (.seq (.block [.sub .r0 .r4 .r3, .lsr .d .r0 .r0 63])
        (.ite (.zero .d .r0) (.block []) (.block [.store .d .r4 .r21 hDlen])))
      (.block [.store .d .r4 .r21 hDlen]))

/-- r's octets: the signature, `q_len`. -/
def ptrR : List Instr := [.load .d .r12 .r21 hSig, .load .d .r6 .r21 hQ]

/-- s's octets: the signature plus `q_len`, `q_len`. -/
def ptrS : List Instr := ptrR ++ [.add .r12 .r12 .r6]

/-- The buffer, `q_len` octets. -/
def ptrBuf : List Instr := [.load .d .r12 .r21 hBuf, .load .d .r6 .r21 hQ]

/-- The buffer from `q_len` on, `q_len` octets. -/
def ptrBuf2 : List Instr := ptrBuf ++ [.add .r12 .r12 .r6]

/-- 0 into array `j`. -/
def zeroArr (j : Nat) : Prog isa := .seq (.block (base .r14 j)) Precompute.zeroWords

/-- `r26 &=` the mask of `0 < [a] < q`, with 0 in array 7. -/
def inRange (a : Nat) : Prog isa :=
  .seq (.block (base .r8 a ++ base .r9 3)) (.seq subMod (.seq (eqMask .r19 a 7)
    (.block (clear19 ++ [.logic .and .r26 .r26 .r20]))))

/-- In the Q space: q in array 0; r into array 5 and s into array 6, and
`r26 :=` the mask of both in range. -/
def ranges : Prog isa :=
  .seq (.block (enterQ ++ ptrR)) (.seq (loadArr 5) (.seq (.block ptrS) (.seq (loadArr 6)
    (.seq (zeroArr 7) (.seq (.block [.li .r26 0, .subi .r26 .r26 1]) (.seq (inRange 5) (inRange 6)))))))

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

/-- The digest's scalar into array 6: its first `hDlen` octets, or 0 if there
are none. -/
def scalar : Prog isa :=
  .seq (.block [.load .d .r12 .r21 hDig, .load .d .r6 .r21 hDlen])
    (.ite (.zero .d .r6) (zeroArr 6) (loadArr 6))

/-- `u1 = z w mod q` into array 6 and `u2 = r w mod q` into array 5, then both
to the buffer. -/
def products : Prog isa :=
  .seq scalar (.seq (.block ptrR) (.seq (loadArr 5) (.seq (copy 1 8) (.seq (.block minv)
    (.seq (montOp 6 6 4) (.seq (montOp 6 6 1) (.seq (montOp 5 5 4) (.seq (montOp 5 5 1)
      (.seq (.block ptrBuf) (.seq (storeBE 6) (.seq (.block ptrBuf2) (storeBE 5))))))))))))

/-- In the P space, the power of the number at `r12` (`p_len` octets) by the
`q_len` octets at `r24`, into array 4. -/
def powP : Prog isa :=
  .seq (.block [.load .d .r6 .r21 hP]) (.seq (loadArr 4) (.seq (copy 1 8)
    (.seq (.block ([.addi .r30 .r24 0, .load .d .r31 .r21 hQ] ++ minv)) (.seq ModExp.powSecret
      (.block [.addi .r31 .r23 0])))))

/-- `v = g^u1 y^u2 mod p` into array 7, then to the buffer (`p_len` octets). -/
def combine : Prog isa :=
  .seq (.block (enterP ++ ptrG ++ [.load .d .r24 .r21 hBuf])) (.seq powP (.seq (copy 9 4)
    (.seq (.block (ptrBuf2 ++ [.addi .r24 .r12 0] ++ ptrY)) (.seq powP (.seq (copy 1 8)
      (.seq (.block minv) (.seq (montOp 5 4 1) (.seq (copy 6 9) (.seq (montOp 7 6 5)
        (.seq (.block [.load .d .r12 .r21 hBuf, .load .d .r6 .r21 hP]) (storeBE 7)))))))))))

/-- In the Q space, `v mod q` (`reduce` of the buffer's `p_len` octets) into
array 1, r into array 5, and `r3 :=` 1 if they are equal and `r26` is all
ones, else 0. -/
def compare : Prog isa :=
  .seq (.block (enterQ ++ [.load .d .r30 .r21 hBuf, .load .d .r31 .r21 hP])) (.seq ModArith.reduce
    (.seq (.block ([.addi .r31 .r23 0] ++ ptrR)) (.seq (loadArr 5) (.seq (eqMask .r3 1 5)
      (.block [.logic .and .r3 .r3 .r26, .li .r0 1, .logic .and .r3 .r3 .r0])))))

/-- The verification, after the check of the key. -/
def body : Prog isa :=
  .seq digestLen (.seq ranges (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products (.seq combine compare))))))

/-- `vg_dsa_verify`. -/
def verify : Prog isa :=
  .seq (.block entry) (.seq (checkKey body (.block [.li .r3 0])) (.block restore))

end VG.Impl.Dsa.PPC64LE.Verify
