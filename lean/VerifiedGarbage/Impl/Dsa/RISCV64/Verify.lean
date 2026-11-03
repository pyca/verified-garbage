module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Common

/-!
# DSA verification on RISC-V

`vg_dsa_verify(key = a0, key_len = a1, p_len = a2, q_len = a3,
signature = a4, signature_len = a5, digest = a6, digest_len = a7,
scratch, scratch_len)`, `scratch` and `scratch_len` on the stack. As on
PPC64LE (`Impl/Dsa/PPC64LE/Verify.lean`), after `checkKey` (`Common.lean`),
which branches on the public key only:

* in the Q space, the mask of `0 < r < q` and `0 < s < q` (`below` and
  `eqMask` with 0), `R² mod q` (`rr`, into arrays 1 and 24), `q − 2`
  (`minus2`) to the buffer, `w = s^(q − 2) mod q` (`powWin` over its
  octets), then `u1 = z w mod q` and `u2 = r w mod q` (two Montgomery
  multiplications each, by w and by R²), for the digest's scalar `z` (its
  first `min(digest_len, bitLength q / 8)` octets), to the buffer at 0 and
  32 (the most octets q has);
* in the P space, `v = g^u1 y^u2 mod p` by one joint power (`combine`): g
  and y into arrays 4 and 5, the table `g^i y^j R mod p` for `i, j < 4`,
  then for each pair of bits of u1 and u2, two squares and a multiplication
  by the entry they select; `v` to the buffer;
* in the Q space, `v mod q` (`reduce64`) compared with r (`eqMask`).

The result is that comparison under the mask: nothing branches on the
signature or the digest, only on their lengths and on the key. The digest's
address is kept in the header (`hDigest`) until its scalar is read.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.Verify

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp one)

/-- `a1 := min(digest_len, 64)`, without a branch: `a7` unless `a7 >> 6` is
not zero. -/
def capD : List Instr :=
  [.shift .srl .d .a1 .a7 6, .li .t3 0, .sub .a1 .t3 .a1, .shift .srl .d .a1 .a1 63, .sub .a1 .t3 .a1,
    .li .t3 64, .logic .xor .t3 .a7 .t3, .logic .and .t3 .t3 .a1, .logic .xor .a1 .a7 .t3]

/-- The working space from the stack, the registers saved there, the key and
the signature into `s11` and `ra`, the digest's address and the lengths into
the header. -/
def entry : List Instr :=
  [.addSp .t2 0, .load .d .t2 .t2 0] ++ save .t2 ++
    [.addi .s11 .a0 0, .addi .ra .a4 0, .store .d .a6 .s6 hDigest] ++ capD ++
    [.shift .sll .d .a1 .a1 48, .shift .sll .d .t3 .a3 16, .add .t3 .a2 .t3, .add .t3 .t3 .a1,
      .store .d .t3 .s6 hLens]

/-- r's octets: the signature, `q_len`. -/
def ptrR : List Instr := [.addi .s7 .ra 0] ++ getQ .s8

/-- s's octets: the signature plus `q_len`, `q_len`. -/
def ptrS : List Instr := ptrR ++ [.add .s7 .s7 .s8]

/-- The buffer, `q_len` octets. -/
def ptrBuf : List Instr := bufBase .s7 .t2 ++ getQ .s8

/-- The buffer from octet 32 on (the most octets q has), `q_len` octets. -/
def ptrBuf2 : List Instr := ptrBuf ++ [.addi .s7 .s7 32]

/-- `a4 &=` the mask of `0 < [a] < q`, with 0 in array 7. -/
def inRange (a : Nat) : Prog isa :=
  .seq (below a) (.seq (eqMask .a2 a 7) (.block (clear ++ [.logic .and .a4 .a4 .a1])))

/-- In the Q space, with q in array 0: r into array 5 and s into array 6,
and `a4 :=` the mask of both in range. -/
def ranges : Prog isa :=
  .seq (.block (enterQ ++ ptrR)) (.seq (loadArr 5) (.seq (.block ptrS) (.seq (loadArr 6)
    (.seq (zeroArr 7) (.seq (.block [.li .a4 (-1)]) (.seq (inRange 5) (inRange 6)))))))

/-- The mask into the header's word `hMask` (secret: it stays in memory). -/
def keepMask : List Instr := [.store .d .a4 .s6 hMask]

/-- `-q⁻¹ mod 2⁶⁴` into `t1`, `R² mod q` into arrays 1 and 24. -/
def rrQ : Prog isa := .seq (.block Precompute.minv) rr

/-- Array 6 := q − 2, word by word from array 0, the borrow in `s4`. -/
def minus2 : Prog isa :=
  .seq (.block (base .t3 0 ++ base .t4 6 ++ [.addi .t5 .t0 0, .li .s4 2]))
    (countLoop .t5 [.load .d .s2 .t3 0, .sltu .s0 .s2 .s4, .sub .s2 .s2 .s4, .addi .s4 .s0 0,
      .store .d .s2 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8])

/-- `q − 2` to the buffer. -/
def qMinus2 : Prog isa := .seq minus2 (.seq (.block ptrBuf) (storeBE 6))

/-- `w = s^(q − 2) mod q` into array 4: s again into array 4, `R² mod q` into
array 1, the power over the buffer's `q_len` octets. -/
def inverse : Prog isa :=
  .seq (.block ptrS) (.seq (loadArr 4) (.seq (copy 1 24)
    (.seq (.block (ptrBuf ++ [.addi .s9 .s7 0, .addi .s10 .s8 0])) ModExp.powWin)))

/-- `s8 := min(digest_len, qb)`: `min(digest_len, 64)` unless above `qb`
(both at most 64). -/
def scalarLen : Prog isa :=
  .seq (.block (getQb .s8 ++ getD .t3 ++ [.sub .a0 .s8 .t3, .shift .srl .d .a0 .a0 63]))
    (.ite (.zero .a0) (.block [.addi .s8 .t3 0]) (.block []))

/-- The digest's scalar into array 6: its first `min(digest_len, qb)`
octets, or 0 if there are none. -/
def scalar : Prog isa :=
  .seq scalarLen (.seq (.block [.load .d .s7 .s6 hDigest]) (.ite (.zero .s8) (zeroArr 6) (loadArr 6)))

/-- `u1 = z w mod q` into array 6 and `u2 = r w mod q` into array 5, then both
to the buffer. -/
def products : Prog isa :=
  .seq scalar (.seq (.block ptrR) (.seq (loadArr 5) (.seq (copy 1 24)
    (.seq (montOp 6 6 4) (.seq (montOp 6 6 1) (.seq (montOp 5 5 4) (.seq (montOp 5 5 1)
      (.seq (.block ptrBuf) (.seq (storeBE 6) (.seq (.block ptrBuf2) (storeBE 5)))))))))))

/-- In the P space, the power of the number at `s7` (`p_len` octets) by the
`q_len` octets at `s9`, into array 4. -/
def powP : Prog isa :=
  .seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (copy 1 24)
    (.seq (.block (getQ .s10)) ModExp.powWin)))

/-- The joint table `T_(i + 4 j) = g^i y^j R mod p` for `i, j < 4`, in arrays
`8 + i + 4 j`, from g in array 4, y in array 5 and `R² mod p` in array 1;
then `a := T_0` in array 6. -/
def jointTable : Prog isa :=
  .seq one (.seq (montOp 8 1 7) (.seq (montOp 9 4 1) (.seq (montOp 12 5 1)
  (.seq (montOp 10 9 9) (.seq (montOp 11 10 9)
  (.seq (montOp 13 12 9) (.seq (montOp 14 12 10) (.seq (montOp 15 12 11)
  (.seq (montOp 16 12 12) (.seq (montOp 17 16 9) (.seq (montOp 18 16 10) (.seq (montOp 19 16 11)
  (.seq (montOp 20 16 12) (.seq (montOp 21 20 9) (.seq (montOp 22 20 10) (.seq (montOp 23 20 11)
    (ModExp.copy 6 8)))))))))))))))))

/-- One joint window, u1's two bits at the top of `s7` and u2's at bits 54–55:
two squares, `a := a T_(d1 + 4 d2)`, then `s7 := s7 << 2`. -/
def jointWindow : Prog isa :=
  .seq (ModExp.sqrOp 6 6 5) (.seq (ModExp.sqrOp 6 6 5)
    (.seq (.block [.shift .srl .d .a1 .s7 62, .shift .srl .d .t3 .s7 54, .logicImm .and .t3 .t3 3,
      .shift .sll .d .t3 .t3 2, .add .a1 .a1 .t3])
    (.seq ModExp.select (.seq (montOp 6 6 5) (.block [.shift .sll .d .s7 .s7 2])))))

/-- The four joint windows of u1's byte at `s9` and u2's 32 bytes on, `s9`
advanced. -/
def jointByte : Prog isa :=
  .seq (.block [.load .b .s7 .s9 0, .shift .sll .d .s7 .s7 56, .load .b .t3 .s9 32,
      .shift .sll .d .t3 .t3 56, .shift .srl .d .t3 .t3 8, .add .s7 .s7 .t3, .addi .s9 .s9 1])
    (.seq jointWindow (.seq jointWindow (.seq jointWindow jointWindow)))

/-- `v = g^u1 y^u2 mod p` into array 4, then to the buffer (`p_len` octets):
g into array 4 and y into array 5, the joint table, the joint windows of
u1's and u2's `q_len` bytes, then out of Montgomery form. -/
def combine : Prog isa :=
  .seq (.block (enterP ++ Precompute.minv ++ ptrBuf ++ [.addi .s9 .s7 0] ++ ptrG)) (.seq (.block (getP .s8))
    (.seq (loadArr 4) (.seq (.block ptrY) (.seq (loadArr 5) (.seq (copy 1 24) (.seq jointTable
    (.seq (.block (getQ .s10)) (.seq (.loop (.seq jointByte (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10))
    (.seq (montOp 4 6 7) (.seq (.block (bufBase .s7 .t2 ++ getP .s8)) (storeBE 4)))))))))))

/-- In the Q space, `v mod q` (`reduce64` of the buffer's `p_len` octets)
into array 1, r into array 5, and `a0 :=` 1 if they are equal and the mask
in `hMask` is all ones, else 0. -/
def compare : Prog isa :=
  .seq (.block (enterQ ++ bufBase .s9 .t2 ++ getP .s10)) (.seq ModArith.reduce64
    (.seq (.block ptrR) (.seq (loadArr 5) (.seq (eqMask .a0 1 5)
      (.block [.load .d .a1 .s6 hMask, .logic .and .a0 .a0 .a1, .logicImm .and .a0 .a0 1])))))

/-- The verification, after the check of the key. -/
def body : Prog isa :=
  .seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products (.seq combine compare))))))

/-- `vg_dsa_verify`. -/
def verify : Prog isa :=
  .seq (.block entry) (.seq (checkKey body (.block [.li .a0 0])) (.block restore))

end VG.Impl.Dsa.RISCV64.Verify
