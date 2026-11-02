module

public import VerifiedGarbage.Impl.RsaOaep.RISCV64

/-!
# RSASSA-PSS verification (RFC 8017 §8.1.2) with a precomputed public key on RISC-V

`vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed(n = a0, n_len = a1, e = a2,
e_len = a3, digest = a4, sig = a5, sig_len = a6, salt_len = a7,
any_salt_len, scratch, scratch_len, pre, pre_len)`, the last five on the
stack, for a hash function `H` (an `Impl.Hmac.Stream.RISCV64.Hash`, its
streaming functions) as both the hash function and MGF1's, which it calls,
with `vg_rsa_public_precomputed_checked`. The steps are those of PPC64LE
(`Impl/RsaPss/PPC64LE.lean`).

It runs in the frame of RSAES-OAEP encryption (`Impl/RsaOaep/RISCV64.lean`)
and uses its MGF1 (`mgfXor`) and its part of `scratch` (`oEm`, `oSt`, `oDig`,
`oCtr`), and more of it: three saved words at `oV`, a copy of the streaming
state at `oBk`, the digest selected at `oSel`, and `M'` at `oY`, which is
past the reach of an immediate and so addressed from `scratch + oY`
(`yBase`). The public operation gets the rest of `scratch` from `oRsa`,
`scratch_len - 1024` words, and writes RSAVP1 of the signature (or zeros)
to `EM`'s place, `k = n_len` bytes at `scratch`.

The values the code keeps across the calls are in `s0`–`s4`: `s0` =
`scratch`, `s1` = `k`, `s2` = `digest`, `s3` = `lo` (1 if `emLen = k - 1`,
else 0), `s4` = `dbLen = emLen - hLen - 1`; and `s5` = `c`, the mask
`0xFF >> (8 emLen - emBits)` of `maskedDB`'s first byte, `s6` = `salt_len`
and `s7` = `any_salt_len` (zero-extended), which are saved at `oV` while
MGF1 uses `s6`–`s11`. Until the public operation, `s8`–`s10` hold `e`,
`e_len` and `sig`, and `t1` the modulus' first byte `n₀`. After MGF1, `s10`
holds the accumulator of failed checks, `s11` the salt's length, `s8` the
index of `DB`'s first nonzero byte, then the length `L` of the salt's prefix
being hashed, `s9` and `s5` the shift's distance and passes, then `s9` the
lengths left.

If `n₀ = 0`, `emLen < hLen + 2` or, for a given salt length, `salt_len >
emLen - hLen - 2` (all public), it returns 0. Otherwise it computes `EM`,
whose bytes are secret from here on, as PPC64LE does: `EM`'s last byte
becomes the OR of the checks of `0xbc`, of the leading byte if `lo = 1` and
of the top bits of `maskedDB`; `DB` is unmasked in place and its top bits
cleared; a scan finds the first nonzero byte of `DB` without branching on
it, whose value must be 1, and the salt's length, which must be `salt_len`
if one is given; then `H' = Hash(0⁸ ‖ mHash ‖ salt)`, for a given salt
length at once, for any salt length after shifting `DB` left by `pos + 1`
bytes in ten passes and hashing every prefix, keeping the salt's. The result
is 1 if the accumulator, ORed with `H' ⊕ H`, is zero. Every branch and
address depends only on the pointers, the lengths, `salt_len`,
`any_salt_len` and `n₀`.
-/

@[expose] public section

namespace VG.Impl.RsaPss.RISCV64

open VG VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.RsaPkcs1Sig.RISCV64 (copyLoop fillLoop)
open VG.Impl.RsaOaep.RISCV64 (argBase oEm oSt oDig oCtr oRsa mgfXor)

/-! ## More of our part of `scratch` -/

/-- `c`, `salt_len` and `any_salt_len`, while MGF1 runs. -/
def oV : Nat := 1352
/-- A copy of the streaming state (at most 192 bytes). -/
def oBk : Nat := 1376
/-- The digest selected (at most 64 bytes). -/
def oSel : Nat := 1568
/-- `M' = 0⁸ ‖ mHash ‖ salt`, and room for `DB`'s shift: 2048 bytes. -/
def oY : Nat := 2048

/-- `d := scratch + oY`. -/
def yBase (d : Reg) : List Instr := [.addi d .s0 2047, .addi d d 1]

variable (H : Hash)

/-! ## The entry -/

/-- The arguments into the registers that keep them; then `n₀` into `t1`,
and `lo`, `c` and `dbLen` from it: with `x` the bits of `n₀ >> 1` smeared
down (`2^b - 1` for the top bit `b` of `n₀`), `lo = (x = 0)` and
`c = x ∨ (0xFF ∧ -lo)`. -/
def prologue : List Instr :=
  [argBase, .load .d .s7 .t6 0, .shift .sll .d .s7 .s7 32, .shift .srl .d .s7 .s7 32, .load .d .s0 .t6 8,
    mov .s1 .a1, mov .s2 .a4, mov .s6 .a7, mov .s8 .a2, mov .s9 .a3, mov .s10 .a5, .load .b .t1 .a0 0,
    .shift .srl .d .t2 .t1 1, .shift .srl .d .t3 .t2 1, .logic .or .t2 .t2 .t3, .shift .srl .d .t3 .t2 2,
    .logic .or .t2 .t2 .t3, .shift .srl .d .t3 .t2 4, .logic .or .t2 .t2 .t3,
    .addi .t3 .t2 (-1), .shift .srl .d .s3 .t3 63, .li .t3 0, .sub .t3 .t3 .s3, .li .t4 0xFF,
    .logic .and .t3 .t3 .t4, .logic .or .s5 .t2 .t3, .sub .s4 .s1 .s3, .addi .s4 .s4 (-(H.D + 1 : Nat))]

/-- 0. -/
def fail : Prog isa := .block [.li .a0 0]

/-! ## The checks -/

/-- In `a0`, 1 if `emLen < hLen + 2`, 0 if not. -/
def chkEm : List Instr := [.sub .a0 .s1 .s3, .addi .a0 .a0 (-(H.D + 2 : Nat)), .shift .srl .d .a0 .a0 63]

/-- `a1 :=` the salt length expected, 0 for any. -/
def expLen : Prog isa := .ite (.zero .s7) (.block [mov .a1 .s6]) (.block [.li .a1 0])

/-- In `a0`, nonzero exactly when the salt length expected (`a1`) is more
than `emLen - hLen - 2`, for `emLen ≥ hLen + 2`: the top bit of `a1`, or of
`(emLen - hLen - 2) - a1`. -/
def chkSalt : List Instr :=
  [.sub .a0 .s1 .s3, .addi .a0 .a0 (-(H.D + 2 : Nat)), .sub .a0 .a0 .a1, .shift .srl .d .a0 .a0 63,
    .shift .srl .d .a2 .a1 63, .logic .or .a0 .a0 .a2]

/-! ## The public operation -/

/-- The arguments of `vg_rsa_public_precomputed_checked`: `EM`'s place (`k`
bytes), `pre` (our stack arguments 3 and 4), `e`, the signature (`k` bytes),
and the rest of `scratch` on the stack (`scratch_len` is our stack argument
2). -/
def pubArgs : List Instr :=
  [.addSp .t0 0, argBase, .li .t1 1024, .shift .sll .d .t1 .t1 3, .add .t1 .s0 .t1, .store .d .t1 .t0 0,
    .load .d .t1 .t6 16, .addi .t1 .t1 (-1024), .store .d .t1 .t0 8, .addi .a0 .s0 oEm, mov .a1 .s1,
    .load .d .a2 .t6 24, .load .d .a3 .t6 32, mov .a4 .s8, mov .a5 .s9, mov .a6 .s10, mov .a7 .s1]

/-! ## `EM` -/

/-- `EM`'s last byte replaced by `(EM[k-1] ⊕ 0xbc) ∨ (EM[lo] ∧ ¬c) ∨
(EM[0] ∧ -lo)`: zero exactly when it is `0xbc`, the top bits of `maskedDB`
are zero and, if `lo = 1`, the leading byte is zero. -/
def acc0 : List Instr :=
  [.add .a1 .s0 .s1, .addi .a1 .a1 (-1), .load .b .a2 .a1 0, .li .a3 0xbc, .logic .xor .a2 .a2 .a3,
    .add .a4 .s0 .s3, .load .b .a3 .a4 0, .li .a5 0xFF, .logic .xor .a5 .a5 .s5, .logic .and .a3 .a3 .a5,
    .logic .or .a2 .a2 .a3, .load .b .a3 .s0 0, .li .a5 0, .sub .a5 .a5 .s3, .logic .and .a3 .a3 .a5,
    .logic .or .a2 .a2 .a3, .store .b .a2 .a1 0]

/-- `c`, `salt_len` and `any_salt_len` to `oV`, while MGF1 runs. -/
def spill : List Instr := [.store .d .s5 .s0 oV, .store .d .s6 .s0 (oV + 8), .store .d .s7 .s0 (oV + 16)]

/-- And back. -/
def reload : List Instr := [.load .d .s5 .s0 oV, .load .d .s6 .s0 (oV + 8), .load .d .s7 .s0 (oV + 16)]

/-- MGF1's registers for unmasking `DB` (`dbLen` bytes at `EM + lo`) with `H`
(`hLen` bytes after it). -/
def dbArgs : List Instr := [.add .s8 .s0 .s3, mov .s9 .s4, .add .s6 .s8 .s4, .li .s7 H.D]

/-- `DB`'s first byte ANDed with `c`. -/
def clearTop : List Instr :=
  [.add .a1 .s0 .s3, .load .b .a2 .a1 0, .logic .and .a2 .a2 .s5, .store .b .a2 .a1 0]

/-! ## The scan -/

/-- `a1` = the byte's address, `a2` = the bytes left, `a3` = its index,
`a4` = all ones while no nonzero byte was seen, `a5` = `pos`, `a6` = the
value there. -/
def scanArgs : List Instr :=
  [.add .a1 .s0 .s3, mov .a2 .s4, .li .a3 0, .li .a4 0, .addi .a4 .a4 (-1), .li .a5 0, .li .a6 0]

/-- A byte: `z = (b = 0)`, `take = a4 ∧ (z - 1)`; `pos ∨= i ∧ take`,
`val ∨= b ∧ take`, `a4 ∧= -z`. -/
def scanBody : List Instr :=
  [.load .b .a7 .a1 0, .addi .t1 .a7 (-1), .shift .srl .d .t1 .t1 63, .addi .t2 .t1 (-1),
    .logic .and .t2 .t2 .a4, .logic .and .t3 .a3 .t2, .logic .or .a5 .a5 .t3, .logic .and .t3 .a7 .t2,
    .logic .or .a6 .a6 .t3, .li .t3 0, .sub .t3 .t3 .t1, .logic .and .a4 .a4 .t3, .addi .a1 .a1 1,
    .addi .a3 .a3 1]

/-- The first nonzero byte of `DB`: its index in `a5`, its value in `a6`
(both 0 if there is none). -/
def scan : Prog isa := .seq (.block scanArgs) (countLoop .a2 scanBody)

/-- The accumulator (`s10`): `EM`'s last byte, ORed with `val ⊕ 1`; the
salt's length `dbLen - pos - 1` into `s11`, and `pos` into `s8`. -/
def posCheck : List Instr :=
  [.add .t1 .s0 .s1, .addi .t1 .t1 (-1), .load .b .s10 .t1 0, .li .t2 1, .logic .xor .a6 .a6 .t2,
    .logic .or .s10 .s10 .a6, .sub .s11 .s4 .a5, .addi .s11 .s11 (-1), mov .s8 .a5]

/-- For a given salt length, the accumulator ORed with its difference from
the salt's. -/
def lenCheck : Prog isa :=
  .ite (.zero .s7) (.block [.logic .xor .t1 .s11 .s6, .logic .or .s10 .s10 .t1]) (.block [])

/-! ## `M'` -/

/-- `n` (at least 1) zeros at `scratch + oY`, `n` from `t5`. -/
def clearY (nset : List Instr) : Prog isa := .seq (.block (yBase .a1 ++ nset ++ [.li .t0 0])) fillLoop

/-- `0⁸ ‖ mHash` at `scratch + oY`, after the bytes `nset` puts in `t5` of
`scratch + oY` cleared. -/
def mPrefix (nset : List Instr) : Prog isa :=
  .seq (clearY nset) (.seq (.block ([mov .a4 .s2] ++ yBase .a1 ++ [.addi .a1 .a1 8, .li .a5 H.D])) copyLoop)

/-- The last `salt_len` bytes of `DB` after `mHash`. -/
def copySalt : Prog isa :=
  .seq (.block ([.add .a4 .s0 .s3, .add .a4 .a4 .s4, .sub .a4 .a4 .s6] ++ yBase .a1 ++
      [.addi .a1 .a1 ((8 + H.D : Nat) : Int), mov .a5 .s6]))
    (.ite (.nonzero .a5) copyLoop (.block []))

/-- `DB` after `mHash`. -/
def copyDb : Prog isa :=
  .seq (.block ([.add .a4 .s0 .s3] ++ yBase .a1 ++ [.addi .a1 .a1 ((8 + H.D : Nat) : Int), mov .a5 .s4])) copyLoop

/-! ## The shift -/

/-- A pass: every byte of `DB`'s place in `M'` replaced by the one `d` (`s9`)
bytes after it if bit 0 of `a` (`s8`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block (yBase .a1 ++ [.addi .a1 .a1 ((8 + H.D : Nat) : Int), .add .a2 .a1 .s9, .li .a3 1,
      .logic .and .a3 .s8 .a3, .li .a4 0, .sub .a3 .a4 .a3, mov .a5 .s4]))
    (countLoop .a5 [.load .b .t1 .a1 0, .load .b .t2 .a2 0, .logic .xor .t2 .t2 .t1, .logic .and .t2 .t2 .a3,
      .logic .xor .t1 .t1 .t2, .store .b .t1 .a1 0, .addi .a1 .a1 1, .addi .a2 .a2 1])

/-- `DB`'s place in `M'` shifted left by `pos + 1` (`a`, from `s8`) bytes,
in ten passes (`s5`), the `j`-th by `d = 2^j` (`s9`). -/
def shift : Prog isa :=
  .seq (.block [.addi .s8 .s8 1, .li .s9 1, .li .s5 10])
    (.loop (.seq (shiftPass H) (.block [.shift .srl .d .s8 .s8 1, .add .s9 .s9 .s9, .addi .s5 .s5 (-1)]))
      (.nonzero .s5))

/-! ## Hashing -/

/-- `init` on the state at `scratch + oSt`. -/
def hInit : Prog isa := .seq (.block [.addi .a0 .s0 oSt]) H.callInit

/-- `update` of the state, after `a1` bytes, with the `a3` bytes at `a2`. -/
def hUpd : Prog isa := .seq (.block [.addi .a0 .s0 oSt]) H.callUpd

/-- `finalize` of the state, after `a1` bytes, to `scratch + oDig`. -/
def hFin : Prog isa := .seq (.block [.addi .a0 .s0 oSt, .addi .a2 .s0 oDig]) H.callFin

/-- For a given salt length: `H' = Hash(M')`, `8 + hLen + salt_len` bytes,
to `scratch + oDig`. -/
def hashFixed : Prog isa :=
  .seq (hInit H) (.seq (.block ([.li .a1 0] ++ yBase .a2 ++ [.addi .a3 .s6 ((8 + H.D : Nat) : Int)]))
    (.seq (hUpd H) (.seq (.block [.addi .a1 .s6 ((8 + H.D : Nat) : Int)]) (hFin H))))

/-- `n` bytes of `scratch + src` to `scratch + dst`. -/
def copyN (src dst n : Nat) : Prog isa :=
  .seq (.block [.addi .a4 .s0 src, .addi .a1 .s0 dst, .li .a5 n]) copyLoop

/-- The digest at `oDig` copied to `oSel` if `L` (`s8`) is the salt's length
(`s11`): XORed in under the mask `-(L = sLen)`. -/
def select : Prog isa :=
  .seq (.block [.logic .xor .t3 .s8 .s11, .addi .t3 .t3 (-1), .shift .srl .d .t3 .t3 63, .li .t4 0,
      .sub .t3 .t4 .t3, .addi .a1 .s0 oDig, .addi .a2 .s0 oSel, .li .a3 H.D])
    (countLoop .a3 [.load .b .t1 .a1 0, .load .b .t2 .a2 0, .logic .xor .t1 .t1 .t2, .logic .and .t1 .t1 .t3,
      .logic .xor .t2 .t2 .t1, .store .b .t2 .a2 0, .addi .a1 .a1 1, .addi .a2 .a2 1])

/-- A length `L` (`s8`; `s9` lengths left): the digest of the first
`8 + hLen + L` bytes of `M'`, kept if `L` is the salt's length; then the
next byte of `M'` absorbed. -/
def lenRound : Prog isa :=
  .seq (copyN oSt oBk H.S) (.seq (.block [.addi .a1 .s8 ((8 + H.D : Nat) : Int)]) (.seq (hFin H)
    (.seq (select H) (.seq (copyN oBk oSt H.S) (.seq (.block ([.addi .a1 .s8 ((8 + H.D : Nat) : Int)] ++
      yBase .a2 ++ [.addi .a2 .a2 ((8 + H.D : Nat) : Int), .add .a2 .a2 .s8, .li .a3 1])) (.seq (hUpd H)
    (.block [.addi .s8 .s8 1, .addi .s9 .s9 (-1)])))))))

/-- For any salt length: `H'` for every length below `dbLen`, the salt's
kept at `scratch + oSel`. -/
def hashAny : Prog isa :=
  .seq (hInit H) (.seq (.block ([.li .a1 0] ++ yBase .a2 ++ [.li .a3 (8 + H.D)])) (.seq (hUpd H)
    (.seq (.block [.li .s8 0, mov .s9 .s4]) (.loop (lenRound H) (.nonzero .s9)))))

/-! ## The result -/

/-- The accumulator ORed with `H' ⊕ H` (`H'` at `scratch + o`), and 1 if it
is zero. -/
def cmpH (o : Nat) : Prog isa :=
  .seq (.block [.add .a1 .s0 .s3, .add .a1 .a1 .s4, .addi .a2 .s0 o, .li .a3 H.D])
    (.seq (countLoop .a3 [.load .b .t1 .a1 0, .load .b .t2 .a2 0, .logic .xor .t1 .t1 .t2,
        .logic .or .s10 .s10 .t1, .addi .a1 .a1 1, .addi .a2 .a2 1])
      (.block [.addi .a0 .s10 (-1), .shift .srl .d .a0 .a0 63]))

/-- The salt's hash and the result: by the public salt-length mode. -/
def finish : Prog isa :=
  .ite (.zero .s7)
    (.seq (mPrefix H [.li .t5 8]) (.seq (copySalt H) (.seq (hashFixed H) (cmpH H oDig))))
    (.seq (mPrefix H [.li .t5 1024, .shift .sll .d .t5 .t5 1]) (.seq (copyDb H) (.seq (shift H)
      (.seq (hashAny H) (cmpH H oSel)))))

/-! ## The function -/

/-- After the checks. -/
def verifyMain : Prog isa :=
  .seq (.block pubArgs) (.seq Impl.RsaPkcs1Sig.RISCV64.pubCall (.seq (.block acc0) (.seq (.block spill)
  (.seq (.block (dbArgs H)) (.seq (mgfXor H) (.seq (.block reload) (.seq (.block clearTop) (.seq scan
  (.seq (.block posCheck) (.seq lenCheck (finish H)))))))))))

/-- The checks, then `verifyMain`. -/
def checks : Prog isa :=
  .ite (.zero .t1) fail
    (.seq (.block (chkEm H)) (.ite (.nonzero .a0) fail
      (.seq expLen (.seq (.block (chkSalt H)) (.ite (.nonzero .a0) fail (verifyMain H))))))

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block (Impl.RsaOaep.RISCV64.save ++ prologue H)) (.seq (checks H) (.block Impl.RsaOaep.RISCV64.restore))

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`. -/
def verifyPrecomputed : Prog isa :=
  .frame (.alloc Impl.RsaOaep.RISCV64.frameBytes) (body H) (.free Impl.RsaOaep.RISCV64.frameBytes)

end VG.Impl.RsaPss.RISCV64
