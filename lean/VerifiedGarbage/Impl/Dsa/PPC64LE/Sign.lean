module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify

/-!
# DSA signing on PPC64LE

`vg_dsa_sign(out = r3, out_len = r4, key = r5, key_len = r6, p_len = r7,
nonce = r8, q_len = r9, digest = r10, digest_len, scratch, scratch_len)`, the
last three on the stack. The entry keeps the key, the nonce and the digest
in `r27`, `r28` and `r26`, the lengths in `r2` and `out` in the header's word
`hOut`, as verification does (`Verify.lean`). After `checkKey`
(`Common.lean`), which branches on the public key only:

* in the P space, the mask of `g^x mod p = y` (`powSecret` over x's octets,
  compared with `eqMask`), and `g^k mod p` to the buffer;
* in the Q space, `r = (g^k mod p) mod q` (`reduce`) into array 9, the masks of
  `0 < k < q`, `0 < x < q` and `r ≠ 0`, `R² mod q`, `q − 2` to the buffer,
  `w = k^(q − 2) mod q`, then `s = w (z + x r) mod q` for the digest's scalar
  `z` (`addMod`: `addArr`, `subMod`, `selectAcc`) and the mask of `s ≠ 0`;
* r and s, selected with 0 by the mask, to `out`; the result is the mask's
  low bit.

A key that fails the checks zeroes `out` and returns 0. Nothing branches on
x, the nonce or the digest, only on their lengths and on the public key.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp minv)
open VG.Impl.MillerRabin.PPC64LE (eqMask copy sel ones)

/-- The header's word that keeps `out`. -/
def hOut : Nat := 8

/-- The working space from the stack (its second argument), the registers
saved there, the key, the nonce and the digest into `r27`, `r28` and `r26`,
`out` into `hOut`, `digest_len` (the stack's first argument) into `r10`, and
the lengths into `r2`. -/
def entry : List Instr :=
  [.addSp .r11 104, .load .d .r11 .r11 0] ++ save .r11 ++
    [.addi .r27 .r5 0, .addi .r28 .r8 0, .addi .r26 .r10 0, .store .d .r3 .r21 hOut, .addSp .r10 96,
      .load .d .r10 .r10 0] ++ Verify.capD ++ [.lsl .r4 .r4 48, .lsl .r0 .r9 16, .add .r2 .r7 .r0, .add .r2 .r2 .r4]

/-- x's octets: the key plus `3 p_len + q_len`, `q_len`. -/
def ptrX : List Instr := ptrY ++ [.add .r12 .r12 .r6] ++ getQ .r6

/-- In the P space: `g^x mod p` compared with y, the mask into `hMask`. -/
def keyPair : Prog isa :=
  .seq (.block (ptrX ++ [.addi .r24 .r12 0] ++ ptrG)) (.seq Verify.powP
    (.seq (.block ptrY) (.seq (loadArr 5) (.seq (eqMask .r3 4 5) (.block [.store .d .r3 .r21 hMask])))))

/-- In the P space: `g^k mod p` to the buffer's first `p_len` octets. -/
def gk : Prog isa :=
  .seq (.block ([.addi .r24 .r28 0] ++ ptrG)) (.seq Verify.powP
    (.seq (.block (bufBase .r12 .r0 ++ getP .r6)) (storeBE 4)))

/-- `r22 &=` the mask of `[a] ≠ 0`, with 0 in array 7. -/
def nonZero (a : Nat) : Prog isa :=
  .seq (.block ones) (.seq (eqMask .r19 a 7) (.block (clear19 ++ [.logic .and .r22 .r22 .r20])))

/-- In the Q space: `r = (g^k mod p) mod q` into array 9, and `hMask &=` the
masks of `0 < k < q`, `0 < x < q` and `r ≠ 0`. -/
def rRanges : Prog isa :=
  .seq (.block (enterQ ++ bufBase .r30 .r0 ++ getP .r31)) (.seq ModArith.reduce
    (.seq (.block [.addi .r31 .r23 0]) (.seq (copy 9 1) (.seq (Verify.zeroArr 7)
      (.seq (.block Verify.ptrR) (.seq (loadArr 6) (.seq (.block ptrX) (.seq (loadArr 5)
        (.seq (.block [.load .d .r22 .r21 hMask]) (.seq (Verify.inRange 6) (.seq (Verify.inRange 5)
          (.seq (nonZero 9) (.block [.store .d .r22 .r21 hMask])))))))))))))

/-- `w = k^(q − 2) mod q` into array 4: k into array 4, `R² mod q` into array
1, the power over the buffer's `q_len` octets. -/
def inverseK : Prog isa :=
  .seq (.block Verify.ptrR) (.seq (loadArr 4) (.seq (copy 1 8)
    (.seq (.block (Verify.ptrBuf ++ [.addi .r30 .r12 0, .addi .r31 .r6 0] ++ minv)) (.seq ModExp.powSecret
      (.block [.addi .r31 .r23 0])))))

/-- The accumulator (`r8`, `n + 1` digits) `:= [r5] + [r16]` (`n = r11` digits each). -/
def addArr : Prog isa :=
  .seq (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .addi .r17 .r11 0, .li .r20 0])
    (.seq (Precompute.countLoop .r17 [.load .w .r0 .r15 0, .load .w .r3 .r16 0, .add .r0 .r0 .r3,
        .add .r0 .r0 .r20, .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4, .addi .r15 .r15 4,
        .addi .r16 .r16 4])
      (.block [.store .w .r20 .r14 0]))

/-- `[o] := [a] + [b] mod m` (m in array 0), through arrays 2 and 3, for
`[a] + [b] < 2 m`. -/
def addMod (o a b : Nat) : Prog isa :=
  .seq (.block (base .r5 a ++ base .r16 b ++ base .r8 2 ++ base .r9 3)) (.seq addArr
    (.seq subMod (.seq (.block (base .r5 o)) selectAcc)))

/-- In the Q space, with w in array 4, `R² mod q` in array 8 and r in array
9: `s = w (z + x r) mod q` into array 6. -/
def sValue : Prog isa :=
  .seq Verify.scalar (.seq (Verify.zeroArr 7) (.seq (addMod 6 6 7)
    (.seq (.block (ptrX ++ [.addi .r30 .r12 0, .addi .r31 .r6 0])) (.seq ModArith.reduce
      (.seq (.block [.addi .r31 .r23 0]) (.seq (copy 5 1) (.seq (copy 1 8) (.seq (.block minv)
        (.seq (montOp 5 5 9) (.seq (montOp 5 5 1) (.seq (addMod 6 6 5) (.seq (montOp 6 6 4)
          (montOp 6 6 1)))))))))))))

/-- r and s, selected with 0 by the mask (`hMask &=` the mask of `s ≠ 0`), to
`out`; `r3 :=` the mask's low bit. -/
def output : Prog isa :=
  .seq (Verify.zeroArr 7) (.seq (.block [.load .d .r22 .r21 hMask]) (.seq (nonZero 6)
    (.seq (.block [.addi .r20 .r22 0]) (.seq (sel 1 9 7) (.seq (sel 2 6 7)
      (.seq (.block ([.load .d .r12 .r21 hOut] ++ getQ .r6)) (.seq (storeBE 1)
        (.seq (.block [.add .r12 .r12 .r6]) (.seq (storeBE 2) (.block [.li .r0 1, .logic .and .r3 .r22 .r0]))))))))))

/-- The signing, after the check of the key. -/
def body : Prog isa :=
  .seq keyPair (.seq gk (.seq rRanges (.seq Verify.rrQ (.seq Verify.qMinus2 (.seq inverseK
    (.seq sValue output))))))

/-- `out`'s `2 q_len` octets := 0, and `r3 := 0`. -/
def zeroOut : Prog isa :=
  .seq (.block ([.load .d .r16 .r21 hOut] ++ getQ .r17 ++ [.add .r17 .r17 .r17, .li .r0 0]))
    (.seq (Precompute.countLoop .r17 [.stb .r0 .r16 0, .addi .r16 .r16 1]) (.block [.li .r3 0]))

/-- `vg_dsa_sign`. -/
def sign : Prog isa :=
  .seq (.block entry) (.seq (checkKey body zeroOut) (.block restore))

end VG.Impl.Dsa.PPC64LE.Sign
