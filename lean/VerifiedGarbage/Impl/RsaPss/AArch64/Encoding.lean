module

public import VerifiedGarbage.Impl.RsaPss.AArch64

/-!
# EMSA-PSS's encoding and its check on AArch64, and RSASSA-PSS around them

`encode` (EMSA-PSS-ENCODE) and `checkEncoding` (EMSA-PSS-VERIFY), for a
Merkle–Damgård hash function `H` as both the hash function and MGF1's, run
the code of `Impl/RsaPss/AArch64.lean` in the same frame (`frameBytes`) and
the same first 8192 bytes of their working space, as on x86-64
(`Impl/RsaPss/X86_64/Encoding.lean`): `encode` stores its arguments in the
slots signing used, with `k = emLen` and `lo = 0`, runs `signEnc` and copies
the encoding out; `checkEncoding` copies the encoding to `scratch + oEm`,
with the same slots, and runs verification's checks (`acc0` to
`FixedSalt.select`). The mask of `maskedDB`'s top bits is `0xFF >> z` for
`z = 8 emLen - emBits`, built a bit at a time (`maskBits`): AArch64 has no
shift by a register here.

`sign` and `verifyPrecomputed` then depend on the hash function only
through the function they call: signing finds `emBits` from the modulus'
first byte `n₀` (`8 k + 55 - clz n₀`, `emBitsB`), lets `encode` write the
encoding at `scratch + oEm + lo` (after a zero byte if `lo = 1`) with the
working space from `scratch + oEnc`, and calls the private-key operation on
the `k` bytes at `scratch + oEm` as before. Verification has the public-key
operation write RSAVP1's result to `scratch`, then calls `checkEncoding` on
its last `emLen` bytes with the working space from the next multiple of 8,
and ANDs the result with 1 if the leading byte is zero or `lo = 0`. Both keep
`emBits`, `emLen` and `lo` in `x24`, `x25` and `x26`, which the calls
preserve.
-/

@[expose] public section

namespace VG.Impl.RsaPss.AArch64

open VG.AArch64
open VG.Impl.MdStream.AArch64 (mov)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaPkcs1Sig.AArch64 (copyLoop)

/-- Bit `j` of the mask: `x11 |= (z < 8 - j) << j`, for `z` in `x9`. -/
def maskBit (j : Nat) : List Instr :=
  [.subImm .x .x12 .x9 (8 - j), .lsr .x .x12 .x12 63, .lsl .x .x12 .x12 j, .logic .orr .x .x11 .x11 .x12]

/-- `sC := 0xFF >> (8 emLen - emBits)` from `emLen` in `x23` and `emBits` in
`r`; `sLo := 0`. -/
def maskBits (r : Reg) : List Instr :=
  [.lsl .x .x9 .x23 3, .sub .x .x9 .x9 r, movi .x11 0] ++ (List.range 8).flatMap maskBit ++ st .x11 sC ++
    [movi .x12 0] ++ st .x12 sLo

/-- `x10` nonzero if `emLen < hLen + 2`, and `x9 := emLen`. -/
def fitH (H : Hash) : List Instr := [mov .x9 .x23, .subImm .x .x10 .x9 (H.D + 2), .lsr .x .x10 .x10 63]

/-- 0 returned. -/
def ret0 : Prog isa := .block [movi .x0 0]

/-! ## `encode`

`encode(em = x0, em_len = x1, digest = x2, salt = x3, salt_len = x4,
em_bits = x5, scratch = x6, scratch_len = x7)`. -/

/-- The registers saved, the arguments into their slots and registers, and
the mask. -/
def encPrologue : List Instr :=
  save ++ ([.str .x .x0 .x16 sOut, .str .x .x2 .x16 sDig, .str .x .x3 .x16 sSalt, .str .x .x4 .x16 sSaltLen,
    mov .x23 .x1, mov .x20 .x6] : List Instr) ++ regsUp ++ maskBits .x5

/-- The encoding's `emLen` bytes copied from `scratch + oEm` to `em`. -/
def copyOut : Prog isa := .seq (.block [.addImm .x .x11 .x20 oEm, ld .x14 sOut, mov .x12 .x23]) copyLoop

variable (H : Hash)

/-- The encoding, its copy, and 1. -/
def encMain : Prog isa := seqs [signEnc H, copyOut, .block [movi .x0 1]]

def encBody : Prog isa :=
  seqs [.block (encPrologue ++ fitH H),
    .ite (.nonzero .x .x10) ret0 (seqs [.block ([ld .x12 sSaltLen] ++ saltFits H),
      .ite (.nonzero .x .x10) ret0 (encMain H)]),
    .block restore]

/-- `vg_rsa_pss_<H>_mgf1_<H>_encode`. -/
def encode : Prog isa := .frame (.alloc frameBytes) (encBody H) (.free frameBytes)

/-! ## `checkEncoding`

`check_encoding(digest = x0, em = x1, em_len = x2, em_bits = x3,
salt_len = x4, any_salt_len = w5, scratch = x6, scratch_len = x7)`. -/

/-- `any_salt_len`'s 32 bits, the registers saved, the arguments into their
slots and registers, and the mask. -/
def chkPrologue : List Instr :=
  ([.addImm .w .x5 .x5 0] : List Instr) ++ save ++ ([.str .x .x0 .x16 sDig, .str .x .x4 .x16 sSaltLen,
    .str .x .x5 .x16 sAny, mov .x23 .x2, mov .x20 .x6] : List Instr) ++ regsUp ++ maskBits .x3

/-- The encoding's `emLen` bytes copied from `em` to `scratch + oEm`. -/
def copyIn : Prog isa := .seq (.block [mov .x11 .x1, .addImm .x .x14 .x20 oEm, mov .x12 .x23]) copyLoop

/-- After the checks of the lengths: verification's checks. -/
def chkMain : Prog isa :=
  seqs [.block dbRegs, .block acc0, mgfXor H, .block clearTop, posScan, posCheck, FixedSalt.select H]

/-- The checks of the lengths: `emLen ≥ hLen + 2`, and the expected salt
fits. -/
def chkBody : Prog isa :=
  seqs [.block chkPrologue, copyIn, .block (fitH H),
    .ite (.nonzero .x .x10) ret0 (seqs [expLen, .block (saltFits H),
      .ite (.nonzero .x .x10) ret0 (chkMain H)]),
    .block restore]

/-- `vg_rsa_pss_<H>_mgf1_<H>_check_encoding`. -/
def checkEncoding : Prog isa := .frame (.alloc frameBytes) (chkBody H) (.free frameBytes)

/-! ## The callers -/

/-- From `k` in `x23` and the modulus' first byte `n₀ ≠ 0` in `x10`:
`emBits = 8 (k - 1) + log₂ n₀ = 8 k + 55 - clz n₀` into `x24`,
`emLen = ⌈emBits / 8⌉` into `x25` and `lo = k - emLen` into `x26`. -/
def emBitsB : List Instr :=
  [.clz .x .x9 .x10, .lsl .x .x24 .x23 3, .addImm .x .x24 .x24 55, .sub .x .x24 .x24 .x9,
    .addImm .x .x25 .x24 7, .lsr .x .x25 .x25 3, .sub .x .x26 .x23 .x25]

/-- Where `encode`'s working space starts in ours. -/
def oEnc : Nat := 4096

/-- The arguments of `encode`: a zero byte at `scratch + oEm`, then `em` at
`scratch + oEm + lo`, the digest, the salt, `emBits`, and the working space
after `oEnc`. -/
def encArgs : List Instr :=
  [.addImm .x .x0 .x20 oEm, movi .x9 0, .strb .x9 .x0 0, .add .x .x0 .x0 .x26, mov .x1 .x25, ld .x2 sDig,
    ld .x3 sSalt, ld .x4 sSaltLen, mov .x5 .x24, .addImm .x .x6 .x20 oEnc, ld .x7 sScrLen,
    .subImm .x .x7 .x7 (oEnc / 8)]

variable (encN : String) (encC : Prog isa) (privN : String) (privC : Prog isa)

/-- The check of the modulus, the encoding, then the private-key
operation. -/
def signCBody : Prog isa :=
  seqs [.block (signPrologue ++ n0 .x2),
    .ite (.zero .x .x10) signFail (seqs [.block (emBitsB ++ encArgs), .call encN encC,
      .ite (.zero .w .x0) signFail (.seq (.block privArgs) (.call privN privC))]),
    .block restore]

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`, calling `encode`. -/
def signC : Prog isa := .frame (.alloc frameBytes) (signCBody encN encC privN privC) (.free frameBytes)

/-- The arguments of the precomputed public operation: its output (`k`
bytes) at `scratch`, `pre` (`pre_len` words), `e`, the signature (`k` bytes),
and the rest of `scratch` after our part. -/
def pubArgsC : List Instr :=
  [.addSp .x16 0, movi .x9 oRsa, .add .x .x9 .x20 .x9, .str .x .x9 .x16 0, ld .x9 sScrLen,
    .subImm .x .x9 .x9 1024, .str .x .x9 .x16 8, mov .x0 .x20, mov .x1 .x23, ld .x2 sPre,
    ld .x3 sPreLen, ld .x4 sE, ld .x5 sEl, ld .x6 sOut, mov .x7 .x23]

/-- `x26 :=` 1 if the leading byte is zero or `lo = 0`, else 0; the
arguments of `checkEncoding`: the digest, the last `emLen` bytes of the
output, `emBits`, the salt length's arguments, and the working space from
`scratch + 8 ⌈k / 8⌉`. -/
def chkArgs : List Instr :=
  [.add .x .x1 .x20 .x26, .ldrb .x9 .x20 0, movi .x10 0, .sub .x .x10 .x10 .x26, .logic .and .x .x9 .x9 .x10,
    .subImm .x .x26 .x9 1, .lsr .x .x26 .x26 63,
    ld .x0 sDig, mov .x2 .x25, mov .x3 .x24, ld .x4 sSaltLen, ld .x5 sAny,
    .addImm .x .x9 .x23 7, .lsr .x .x9 .x9 3, ld .x7 sScrLen, .sub .x .x7 .x7 .x9, .lsl .x .x9 .x9 3,
    .add .x .x6 .x20 .x9]

variable (chkN : String) (chkC : Prog isa) (pubN : String) (pubC : Prog isa)

def verifyCBody : Prog isa :=
  seqs [.block (verifyPrologue ++ n0 .x0),
    .ite (.zero .x .x10) verifyFail (seqs [.block (emBitsB ++ pubArgsC), .call pubN pubC, .block chkArgs,
      .call chkN chkC, .block [.logic .and .x .x0 .x0 .x26]]),
    .block restore]

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, calling `checkEncoding`. -/
def verifyC : Prog isa := .frame (.alloc frameBytes) (verifyCBody chkN chkC pubN pubC) (.free frameBytes)

end VG.Impl.RsaPss.AArch64
