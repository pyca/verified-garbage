module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Verify

/-!
# DSA signing on RISC-V

`vg_dsa_sign(out = a0, out_len = a1, key = a2, key_len = a3, p_len = a4,
nonce = a5, q_len = a6, digest = a7, digest_len, scratch, scratch_len)`, the
last three on the stack. As on PPC64LE (`Impl/Dsa/PPC64LE/Sign.lean`): the
entry keeps the key and the nonce in `s11` and `ra`, and the digest's
address, `out` and the lengths in the header (`hDigest`, `hOut`, `hLens`).
After `checkKey` (`Common.lean`), which branches on the public key only:

* in the P space, the mask of `g^x mod p = y` (`powWin` over x's octets,
  compared with `eqMask`), and `g^k mod p` to the buffer;
* in the Q space, `r = (g^k mod p) mod q` (`reduce64`) into array 25 (above
  `powWin`'s arrays), the
  masks of `0 < k < q`, `0 < x < q` and `r ≠ 0`, `R² mod q`, `q − 2` to the
  buffer, `w = k^(q − 2) mod q`, then `s = w (z + x r) mod q` for the
  digest's scalar `z` (`addMod`: `addArr`, `subMod64`, `selectAcc64`) and the
  mask of `s ≠ 0`;
* r and s, selected with 0 by the mask, to `out`; the result is the mask's
  low bit.

A key that fails the checks zeroes `out` and returns 0. Nothing branches on
x, the nonce or the digest, only on their lengths and on the public key.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.Sign

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)

/-- The header's byte offset of `out`. -/
def hOut : Nat := 24

/-- The working space from the stack (its second argument), the registers
saved there, the key and the nonce into `s11` and `ra`, the digest's
address, `out` and the lengths into the header, `digest_len` (the stack's
first argument) into `a7` for `capD`. -/
def entry : List Instr :=
  [.addSp .t2 8, .load .d .t2 .t2 0] ++ save .t2 ++
    [.addi .s11 .a2 0, .addi .ra .a5 0, .store .d .a7 .s6 hDigest, .store .d .a0 .s6 hOut, .addSp .t3 0,
      .load .d .a7 .t3 0] ++ Verify.capD ++
    [.shift .sll .d .a1 .a1 48, .shift .sll .d .t3 .a6 16, .add .t3 .a4 .t3, .add .t3 .t3 .a1,
      .store .d .t3 .s6 hLens]

/-- x's octets: the key plus `3 p_len + q_len`, `q_len`. -/
def ptrX : List Instr := ptrY ++ [.add .s7 .s7 .s8] ++ getQ .s8

/-- In the P space: `g^x mod p` compared with y, the mask into `hMask`. -/
def keyPair : Prog isa :=
  .seq (.block (ptrX ++ [.addi .s9 .s7 0] ++ ptrG)) (.seq Verify.powP
    (.seq (.block ptrY) (.seq (loadArr 5) (.seq (eqMask .a0 4 5) (.block [.store .d .a0 .s6 hMask])))))

/-- In the P space: `g^k mod p` to the buffer's first `p_len` octets. -/
def gk : Prog isa :=
  .seq (.block ([.addi .s9 .ra 0] ++ ptrG)) (.seq Verify.powP
    (.seq (.block (bufBase .s7 .t2 ++ getP .s8)) (storeBE 4)))

/-- `a4 &=` the mask of `[a] ≠ 0`, with 0 in array 7. -/
def nonZero (a : Nat) : Prog isa :=
  .seq (.block [.li .a1 (-1)]) (.seq (eqMask .a2 a 7) (.block (clear ++ [.logic .and .a4 .a4 .a1])))

/-- In the Q space: `r = (g^k mod p) mod q` into array 25, and `hMask &=` the
masks of `0 < k < q`, `0 < x < q` and `r ≠ 0`. -/
def rRanges : Prog isa :=
  .seq (.block (enterQ ++ bufBase .s9 .t2 ++ getP .s10)) (.seq ModArith.reduce64
    (.seq (copy 25 1) (.seq (zeroArr 7)
      (.seq (.block Verify.ptrR) (.seq (loadArr 6) (.seq (.block ptrX) (.seq (loadArr 5)
        (.seq (.block [.load .d .a4 .s6 hMask]) (.seq (Verify.inRange 6) (.seq (Verify.inRange 5)
          (.seq (nonZero 25) (.block [.store .d .a4 .s6 hMask]))))))))))))

/-- `w = k^(q − 2) mod q` into array 4: k into array 4, `R² mod q` into array
1, the power over the buffer's `q_len` octets. -/
def inverseK : Prog isa :=
  .seq (.block Verify.ptrR) (.seq (loadArr 4) (.seq (copy 1 24)
    (.seq (.block (Verify.ptrBuf ++ [.addi .s9 .s7 0, .addi .s10 .s8 0])) ModExp.powWin)))

/-- The accumulator (`a5`, `w + 1` words) `:= [a3] + [a4]` (`w` words each),
the carry in `s4`. -/
def addArr : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t4 .a3 0, .addi .t2 .a4 0, .addi .t5 .t0 0, .li .s4 0])
    (.seq (countLoop .t5 [.load .d .s2 .t4 0, .load .d .s3 .t2 0, .add .s2 .s2 .s3, .sltu .s0 .s2 .s3,
        .add .s2 .s2 .s4, .sltu .s1 .s2 .s4, .logic .or .s4 .s0 .s1, .store .d .s2 .t3 0, .addi .t3 .t3 8,
        .addi .t4 .t4 8, .addi .t2 .t2 8])
      (.block [.store .d .s4 .t3 0]))

/-- `[o] := [a] + [b] mod m` (m in array 0), through arrays 2 and 3, for
`[a] + [b] < 2 m`. -/
def addMod (o a b : Nat) : Prog isa :=
  .seq (.block (base .a3 a ++ base .a4 b ++ base .a5 2 ++ base .a6 3 ++ base .a2 o)) (.seq addArr
    (.seq subMod64 selectAcc64))

/-- `[o] := s4 ? [a] : [b]`, word by word. -/
def sel (o a b : Nat) : Prog isa :=
  .seq (.block (base .a2 o ++ base .a5 a ++ base .a6 b)) selectAcc64

/-- In the Q space, with w in array 4, `R² mod q` in array 24 and r in array
25: `s = w (z + x r) mod q` into array 6. -/
def sValue : Prog isa :=
  .seq Verify.scalar (.seq (zeroArr 7) (.seq (addMod 6 6 7)
    (.seq (.block (ptrX ++ [.addi .s9 .s7 0, .addi .s10 .s8 0])) (.seq ModArith.reduce64
      (.seq (copy 5 1) (.seq (copy 1 24)
        (.seq (montOp 5 5 25) (.seq (montOp 5 5 1) (.seq (addMod 6 6 5) (.seq (montOp 6 6 4)
          (montOp 6 6 1)))))))))))

/-- r and s, selected with 0 by the mask (`hMask &=` the mask of `s ≠ 0`), to
`out`; `a0 :=` the mask's low bit. -/
def output : Prog isa :=
  .seq (zeroArr 7) (.seq (.block [.load .d .a4 .s6 hMask]) (.seq (nonZero 6)
    (.seq (.block [.addi .s4 .a4 0]) (.seq (sel 1 25 7) (.seq (sel 2 6 7)
      (.seq (.block ([.load .d .s7 .s6 hOut] ++ getQ .s8)) (.seq (storeBE 1)
        (.seq (.block [.add .s7 .s7 .s8]) (.seq (storeBE 2) (.block [.logicImm .and .a0 .a4 1]))))))))))

/-- The signing, after the check of the key. -/
def body : Prog isa :=
  .seq keyPair (.seq gk (.seq rRanges (.seq Verify.rrQ (.seq Verify.qMinus2 (.seq inverseK
    (.seq sValue output))))))

/-- `out`'s `2 q_len` octets := 0, and `a0 := 0`. -/
def zeroOut : Prog isa :=
  .seq (.block ([.load .d .t4 .s6 hOut] ++ getQ .t5 ++ [.add .t5 .t5 .t5, .li .s0 0]))
    (.seq (countLoop .t5 [.store .b .s0 .t4 0, .addi .t4 .t4 1]) (.block [.li .a0 0]))

/-- `vg_dsa_sign`. -/
def sign : Prog isa :=
  .seq (.block entry) (.seq (checkKey body zeroOut) (.block restore))

end VG.Impl.Dsa.RISCV64.Sign
