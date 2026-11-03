module

public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Impl.Rsa.RISCV64.Priv

/-!
# RSASSA-PSS signing (RFC 8017 §8.1.1) on RISC-V

`vg_rsa_pss_<H>_mgf1_<H>_sign(out = a0, out_len = a1, n = a2, n_len = a3,
e = a4, e_len = a5, p = a6, p_len = a7, q, q_len, dp, dp_len, dq, dq_len,
qinv, qinv_len, digest, salt, salt_len, scratch, scratch_len)`, the last
thirteen on the stack, for a hash function `H` (an
`Impl.Hmac.Stream.RISCV64.Hash`, its streaming functions) as both the hash
function and MGF1's, which it calls, with `vg_rsa_private_checked`. The
steps are those of PPC64LE (`Impl/RsaPss/PPC64LE/Sign.lean`).

It runs in the frame of RSAES-OAEP encryption (`Impl/RsaOaep/RISCV64.lean`),
with its part of `scratch` and its MGF1 (`mgfXor`), and hashes
`M' = 0⁸ ‖ mHash ‖ salt` at `oY` as verification does for a given salt length
(`Impl/RsaPss/RISCV64.lean`, `hashFixed`). The values the code keeps across
the calls are in `s0`–`s4`, all public: `s0` = `scratch`, `s1` = `k = n_len`,
`s2` = `out`, `s3` = `lo` (1 if `emLen = k - 1`, else 0, from the modulus'
first byte `n₀`, as verification computes it) and `s4` = `salt_len`. `n`,
`e`, `e_len`, `p` and `p_len`, which arrive in registers and are only needed
for the private operation and the mask of `DB`'s top bits, are saved in our
part of `scratch` at `oP`, past what MGF1 and the hash calls write; the
digest, the salt and the rest of the key are read from our stack arguments.

If `n₀ = 0`, `emLen < hLen + 2` or `salt_len > emLen - hLen - 2` (all public),
it writes zeros to `out` and returns 0. Otherwise it writes `M'` and hashes it
to `H` (at `oDig`); writes `EM` at `scratch`: zeros, `0x01` at
`k - salt_len - hLen - 2`, the salt after it, `H` at `k - hLen - 1` and
`0xbc` last; masks `DB` (`dbLen = k - lo - hLen - 1` bytes at `lo`) with
MGF1 of `H`, and clears its top bits with the mask `c` of verification; and
calls `vg_rsa_private_checked` on `EM`, from a frame of `privBytes` bytes
below ours that holds its twelve stack arguments, as RSAES-OAEP decryption
does. That function writes the signature (or zeros) to `out`, and its result
is ours. Every branch and address depends only on the pointers, the lengths
and `n₀`; the digest and the salt are only copied and hashed.
-/

@[expose] public section

namespace VG.Impl.RsaPss.RISCV64.Sign

open VG VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Impl.RsaPkcs1Sig.RISCV64 (copyLoop fillLoop)
open VG.Impl.RsaOaep.RISCV64 (frameBytes argBase save restore encFail oEm oDig oRsa mgfXor clearEm)
open VG.Impl.RsaPss.RISCV64 (oY yBase clearY hashFixed)

/-! ## The saved arguments -/

/-- `n`, `e`, `e_len`, `p` and `p_len`, five words. -/
def oP : Nat := 1352

/-! ## The entry -/

/-- `t2 := ` the bits of `t1 >> 1` smeared down, and `s3 := lo`. -/
def smear : List Instr :=
  [.shift .srl .d .t2 .t1 1, .shift .srl .d .t3 .t2 1, .logic .or .t2 .t2 .t3, .shift .srl .d .t3 .t2 2,
    .logic .or .t2 .t2 .t3, .shift .srl .d .t3 .t2 4, .logic .or .t2 .t2 .t3, .addi .t3 .t2 (-1),
    .shift .srl .d .s3 .t3 63]

/-- The arguments into the registers that keep them, and `n`, `e`, `e_len`,
`p` and `p_len` to `scratch + oP`; then `n₀` into `t1` and `lo` into `s3`. -/
def prologue : List Instr :=
  [argBase, .load .d .s0 .t6 88, mov .s1 .a3, mov .s2 .a0, .load .d .s4 .t6 80, .store .d .a2 .s0 oP,
    .store .d .a4 .s0 (oP + 8), .store .d .a5 .s0 (oP + 16), .store .d .a6 .s0 (oP + 24),
    .store .d .a7 .s0 (oP + 32), .load .b .t1 .a2 0] ++ smear

variable (H : Hash)

/-! ## The checks -/

/-- In `a0`, 1 if `emLen < hLen + 2`, 0 if not. -/
def chkEm : List Instr := [.sub .a0 .s1 .s3, .addi .a0 .a0 (-(H.D + 2 : Nat)), .shift .srl .d .a0 .a0 63]

/-- In `a0`, nonzero exactly when `salt_len > emLen - hLen - 2`, for
`emLen ≥ hLen + 2`: the top bit of `salt_len`, or of
`(emLen - hLen - 2) - salt_len`. -/
def chkSalt : List Instr :=
  [.sub .a0 .s1 .s3, .addi .a0 .a0 (-(H.D + 2 : Nat)), .sub .a0 .a0 .s4, .shift .srl .d .a0 .a0 63,
    .shift .srl .d .a2 .s4 63, .logic .or .a0 .a0 .a2]

/-! ## `M'` and its hash -/

/-- `salt_len` bytes of the salt (our stack argument 9) to `a1`, if it is not
empty. -/
def copySalt : Prog isa :=
  .seq (.block [argBase, .load .d .a4 .t6 72, mov .a5 .s4]) (.ite (.nonzero .a5) copyLoop (.block []))

/-- `M' = 0⁸ ‖ mHash ‖ salt` at `scratch + oY`. -/
def mPrime : Prog isa :=
  .seq (clearY [.li .t5 8])
    (.seq (.seq (.block ([argBase, .load .d .a4 .t6 64] ++ yBase .a1 ++ [.addi .a1 .a1 8, .li .a5 H.D]))
      copyLoop)
      (.seq (.block (yBase .a1 ++ [.addi .a1 .a1 ((8 + H.D : Nat) : Int)])) copySalt))

/-- `H = Hash(M')` to `scratch + oDig`, with `salt_len` in `s6`. -/
def hashM : Prog isa := .seq (.block [mov .s6 .s4]) (hashFixed H)

/-! ## `EM` -/

/-- `0x01` at `EM + k - salt_len - hLen - 2`, and the salt after it. -/
def putSalt : Prog isa :=
  .seq (.block [.add .a1 .s0 .s1, .sub .a1 .a1 .s4, .addi .a1 .a1 (-(H.D + 2 : Nat)), .li .t1 1,
      .store .b .t1 .a1 0, .addi .a1 .a1 1]) copySalt

/-- `H` at `EM + k - hLen - 1`, and `0xbc` at `EM + k - 1`. -/
def putH : Prog isa :=
  .seq (.seq (.block [.addi .a4 .s0 oDig, .add .a1 .s0 .s1, .addi .a1 .a1 (-(H.D + 1 : Nat)), .li .a5 H.D])
      copyLoop)
    (.block [.add .a1 .s0 .s1, .addi .a1 .a1 (-1), .li .t1 0xbc, .store .b .t1 .a1 0])

/-- MGF1's registers for masking `DB` (`dbLen` bytes at `EM + lo`) with `H`
(`hLen` bytes at `EM + k - hLen - 1`). -/
def dbArgs : List Instr :=
  [.add .s6 .s0 .s1, .addi .s6 .s6 (-(H.D + 1 : Nat)), .li .s7 H.D, .add .s8 .s0 .s3, .sub .s9 .s1 .s3,
    .addi .s9 .s9 (-(H.D + 1 : Nat))]

/-- `DB`'s first byte ANDed with `c = smear(n₀ >> 1) ∨ (0xFF ∧ -lo)`, from
`n₀` again. -/
def clearTop : List Instr :=
  [.load .d .t1 .s0 oP, .load .b .t1 .t1 0, .shift .srl .d .t2 .t1 1, .shift .srl .d .t3 .t2 1,
    .logic .or .t2 .t2 .t3, .shift .srl .d .t3 .t2 2, .logic .or .t2 .t2 .t3, .shift .srl .d .t3 .t2 4,
    .logic .or .t2 .t2 .t3, .li .t3 0, .sub .t3 .t3 .s3, .li .t4 0xFF, .logic .and .t3 .t3 .t4,
    .logic .or .t2 .t2 .t3, .add .a1 .s0 .s3, .load .b .a2 .a1 0, .logic .and .a2 .a2 .t2,
    .store .b .a2 .a1 0]

/-! ## The private operation -/

/-- The frame from which `vg_rsa_private_checked` is called: its twelve
stack arguments, at its `sp`. -/
def privBytes : Nat := 96

/-- `vg_rsa_private_checked`. -/
def privCall : Prog isa := .call "vg_rsa_private_checked" Impl.Rsa.RISCV64.Priv.code

/-- Our stack argument `j` (`q` … `qinv_len`) to its stack argument
`j + 2`. -/
def copyArg (j : Nat) : List Instr := [.load .d .t1 .t6 (8 * j), .store .d .t1 .t0 (8 * (j + 2))]

/-- Its arguments, with `t0` its `sp` and `t6` our first stack argument: on
the stack `p` and `p_len` (saved at `oP`) and our stack arguments 0 to 7,
then the rest of `scratch` from `oRsa` and `scratch_len - 1024`; in the
registers `out` (`k` bytes), `n`, `e` (saved at `oP`) and `EM` (`k`
bytes). -/
def privArgs : List Instr :=
  [.addSp .t0 0, .addSp .t6 (privBytes + frameBytes), .load .d .t1 .s0 (oP + 24), .store .d .t1 .t0 0,
    .load .d .t1 .s0 (oP + 32), .store .d .t1 .t0 8] ++ (List.range 8).flatMap copyArg ++
    [.li .t1 1024, .shift .sll .d .t1 .t1 3, .add .t1 .s0 .t1, .store .d .t1 .t0 80, .load .d .t1 .t6 96,
      .addi .t1 .t1 (-1024), .store .d .t1 .t0 88, mov .a0 .s2, mov .a1 .s1, .load .d .a2 .s0 oP, mov .a3 .s1,
      .load .d .a4 .s0 (oP + 8), .load .d .a5 .s0 (oP + 16), .addi .a6 .s0 oEm, mov .a7 .s1]

/-- The private operation, from its frame. -/
def priv : Prog isa := .frame (.alloc privBytes) (.seq (.block privArgs) privCall) (.free privBytes)

/-! ## The function -/

/-- After the checks: `M'` and `H`, `EM`, and the private operation. -/
def signMain : Prog isa :=
  .seq (mPrime H) (.seq (hashM H) (.seq clearEm (.seq (putSalt H) (.seq (putH H)
    (.seq (.block (dbArgs H)) (.seq (mgfXor H) (.seq (.block clearTop) priv)))))))

/-- The checks, then `signMain`. -/
def checks : Prog isa :=
  .ite (.zero .t1) encFail
    (.seq (.block (chkEm H)) (.ite (.nonzero .a0) encFail
      (.seq (.block (chkSalt H)) (.ite (.nonzero .a0) encFail (signMain H)))))

/-- The frame's body. -/
def body : Prog isa := .seq (.block (save ++ prologue)) (.seq (checks H) (.block restore))

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`. -/
def sign : Prog isa := .frame (.alloc frameBytes) (body H) (.free frameBytes)

end VG.Impl.RsaPss.RISCV64.Sign
