module

public import VerifiedGarbage.Impl.RsaPss.X86_64

/-!
# EMSA-PSS's encoding and its check on x86-64, and RSASSA-PSS around them

`encode` (EMSA-PSS-ENCODE) and `checkEncoding` (EMSA-PSS-VERIFY), for a
Merkle–Damgård hash function `H` as both the hash function and MGF1's, run
the code of `Impl/RsaPss/X86_64.lean` in the same frame (`frameBytes`) and
the same first 8192 bytes of their working space: `encode` stores its
arguments in the slots signing used, with `k = emLen` and `lo = 0`, runs
`signEnc` and copies the encoding out; `checkEncoding` copies the encoding
to `scratch + oEm`, with the same slots, and runs verification's checks
(`acc0` to `saltBack`). The mask of `maskedDB`'s top bits is `0xFF >> z`
for `z = 8 emLen - emBits`, by a shift of `cl`.

`sign` and `verifyPrecomputed` then depend on the hash function only
through the function they call: signing finds `emBits` from the modulus'
first byte `n₀` (`8 (k - 1) + log₂ n₀`, by seven compares), lets `encode`
write the encoding at `scratch + oEm + lo` (after a zero byte if
`lo = 1`) with the working space from `scratch + 4096`, and calls the
private-key operation on the `k` bytes at `scratch + oEm` as before.
Verification has the public-key operation write RSAVP1's result to
`scratch`, then calls `checkEncoding` on its last `emLen` bytes with the
working space from the next multiple of 8, and ANDs the result with the
mask of the leading byte being zero if `lo = 1`.
-/

@[expose] public section

namespace VG.Impl.RsaPss.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- The slot of `emBits` (signing and verifying; free there). -/
def sBits : Nat := sL
/-- The slot of `emLen`. -/
def sEml : Nat := sNb

/-- `sC := 0xFF >> (8 emLen - emBits)` from `emLen` in `sK` and `emBits` in
`r`; `sLo := 0`. -/
def maskBits (r : Reg) : List Instr :=
  [.mov .rax (.mem (sp sK)), .shift .shl .rax 3, .alu .sub .rax (.reg r), .mov .rcx (.reg .rax),
    .mov32 .rax (.imm 0xFF), .shiftCl .shr .rax, .store (sp sC) .rax, .mov32 .rax (.imm 0),
    .store (sp sLo) .rax]

variable (H : Hash)

/-- CF set if `emLen < hLen + 2`. -/
def fitH : List Instr := [.mov .rax (.mem (sp sK)), .alu .cmp .rax (.imm (BitVec.ofNat 32 (H.D + 2)))]

/-- 0 returned. -/
def ret0 : Prog isa := .block [.mov32 .rax (.imm 0)]

/-! ## `encode`

`encode(em = rdi, em_len = rsi, digest = rdx, salt = rcx, salt_len = r8,
em_bits = r9, scratch, scratch_len)`, the last two on the stack. -/

/-- The arguments into their slots, and the mask. -/
def encPrologue : List Instr :=
  saveRegs ++ ([.store (sp sOut) .rdi, .store (sp sK) .rsi, .store (sp sDig) .rdx, .store (sp sSalt) .rcx,
    .store (sp sSaltLen) .r8, .mov .rax (.mem (arg 0)), .store (sp sScr) .rax] : List Instr) ++ maskBits .r9

/-- The encoding's `emLen` bytes copied from `scratch + oEm` to `em`. -/
def copyOut : Prog isa :=
  .seq (.block (scr .rsi oEm ++ ([.mov .rdi (.mem (sp sOut)), .mov .r10 (.mem (sp sK)), .mov32 .r8 (.imm 0)] :
      List Instr)))
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.reg .r10))

/-- The encoding, its copy, and 1. -/
def encMain : Prog isa := seqs [signEnc H, copyOut, .block [.mov32 .rax (.imm 1)]]

def encBody : Prog isa :=
  seqs [.block (encPrologue ++ fitH H),
    .ite .b ret0 (seqs [.block (([.mov .rdx (.mem (sp sSaltLen))] : List Instr) ++ saltFits H),
      .ite .b ret0 (encMain H)]),
    .block restoreRegs]

/-- `vg_rsa_pss_<H>_mgf1_<H>_encode`. -/
def encode : Prog isa := .frame (.alloc frameBytes) (encBody H) (.free frameBytes)

/-! ## `checkEncoding`

`check_encoding(digest = rdi, em = rsi, em_len = rdx, em_bits = rcx,
salt_len = r8, any_salt_len = r9d, scratch, scratch_len)`, the last two on
the stack. -/

/-- The arguments into their slots, and the mask. -/
def chkPrologue : List Instr :=
  saveRegs ++ ([.store (sp sDig) .rdi, .store (sp sSig) .rsi, .store (sp sK) .rdx, .store (sp sSlen) .r8,
    .mov .rax (.mem (arg 0)), .store (sp sScr) .rax] : List Instr) ++ maskBits .rcx

/-- The encoding's `emLen` bytes copied from `em` to `scratch + oEm`. -/
def copyIn : Prog isa :=
  .seq (.block (scr .rcx oEm ++ ([.mov .rsi (.mem (sp sSig)), .mov .r10 (.mem (sp sK)), .mov32 .r8 (.imm 0)] :
      List Instr)))
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8) .rax] (.reg .r10))

/-- `sAny := any_salt_len ≠ 0`; `rdx` the expected length for the check, 0
if any. -/
def anyReg : Prog isa :=
  .seq (.block [.mov32 .rax (.reg .r9), .alu .test .rax (.reg .rax)])
    (.ite .e (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))])
      (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]))

/-- After the checks: `rax = emLen - hLen - 2`. -/
def chkMain : Prog isa :=
  seqs [.block dbSlots, .block acc0, mgfXor H, .block clearTop, scanCheck H, saltBack H]

/-- The checks of the lengths: `emLen ≥ hLen + 2`, and the expected salt
fits. -/
def chkBody : Prog isa :=
  seqs [.block chkPrologue, copyIn, anyReg, .block (fitH H),
    .ite .b ret0 (seqs [.block (([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)), .alu .sub .rax (.reg .r8)] :
        List Instr) ++ saltFits H),
      .ite .b ret0 (chkMain H)]),
    .block restoreRegs]

/-- `vg_rsa_pss_<H>_mgf1_<H>_check_encoding`. -/
def checkEncoding : Prog isa := .frame (.alloc frameBytes) (chkBody H) (.free frameBytes)

/-! ## The callers -/

/-- `rax`, the modulus' first byte `n₀ ≠ 0`, to `emBits = 8 (k - 1) + log₂ n₀`
(`sBits`), `emLen = ⌈emBits / 8⌉` (`sEml`) and `lo = k - emLen` (`sLo`). -/
def emBitsB : List Instr :=
  [.mov .rdx (.mem (sp sK)), .shift .shl .rdx 3, .alu .sub .rdx (.imm 1)] ++
    ((List.range 7).flatMap fun i =>
      ([.alu .cmp .rax (.imm (BitVec.ofNat 32 (2 ^ (i + 1)))), .alu .sbb .rdx (.imm 0)] : List Instr)) ++
    [.store (sp sBits) .rdx, .mov .rax (.reg .rdx), .alu .add .rax (.imm 7), .shift .shr .rax 3,
      .store (sp sEml) .rax, .mov .r8 (.mem (sp sK)), .alu .sub .r8 (.reg .rax), .store (sp sLo) .r8]

/-- Where `encode`'s working space starts in ours. -/
def oEnc : Nat := 4096

/-- The arguments of `encode`: a zero byte at `scratch + oEm`, then `em` at
`scratch + oEm + lo`, the digest, the salt, `emBits`, and the working space
after `oEnc`. -/
def encArgs : List Instr :=
  scr .rdi oEm ++ ([.mov32 .rax (.imm 0), .store8 (at_ .rdi) .rax, .alu .add .rdi (.mem (sp sLo)),
    .mov .rsi (.mem (sp sEml)), .mov .rdx (.mem (sp sDig)), .mov .rcx (.mem (sp sSalt)),
    .mov .r8 (.mem (sp sSaltLen)), .mov .r9 (.mem (sp sBits))] : List Instr) ++
  scr .rax oEnc ++ ([.store (sp 0) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm (BitVec.ofNat 32 (oEnc / 8))),
    .store (sp 8) .rax] : List Instr)

variable (encN : String) (encC : Prog isa) (privN : String) (privC : Prog isa)

/-- The checks on the modulus, the encoding, then the private-key
operation. -/
def signCBody : Prog isa :=
  seqs [.block (signPrologue ++ n0),
    .ite .e signFail (seqs [.block (emBitsB ++ encArgs), .call encN encC,
      .block [.alu32 .test .rax (.reg .rax)],
      .ite .e signFail (.seq (.block privArgs) (.call privN privC))]),
    .block restoreRegs]

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`, calling `encode`. -/
def signC : Prog isa := .frame (.alloc frameBytes) (signCBody encN encC privN privC) (.free frameBytes)

/-- The arguments of the public-key operation, with the caller's cached
modulus: its output (`k` bytes) at `scratch`, the signature, and the rest
of `scratch` after our part. -/
def pubArgsC : List Instr :=
  ([.mov .rax (.mem (sp sSig)), .store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] : List Instr) ++
  scr .rax oRsa ++ ([.store (sp 16) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 24) .rax, .mov .rdi (.mem (sp sScr)), .mov .rsi (.mem (sp sK)), .mov .rdx (.mem (arg 5)),
    .mov .rcx (.mem (arg 6)), .mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))] : List Instr)

/-- `sAcc :=` all ones if the leading byte is zero or `lo = 0`, else 0; the
arguments of `checkEncoding`: the digest, the last `emLen` bytes of the
output, `emBits`, the salt length's arguments, and the working space from
`scratch + 8 ⌈k / 8⌉`. -/
def chkArgs : List Instr :=
  [.mov .rcx (.mem (sp sScr)), .movzx8 .r9 (at_ .rcx), .mov .r10 (.mem (sp sLo)), .mov32 .r11 (.imm 0),
    .alu .sub .r11 (.reg .r10), .alu .and .r9 (.reg .r11), .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9),
    .store (sp sAcc) .r9,
    .mov .rdi (.mem (sp sDig)), .mov .rsi (.reg .rcx), .alu .add .rsi (.reg .r10), .mov .rdx (.mem (sp sEml)),
    .mov .r8 (.mem (arg 1)), .mov .r9 (.mem (arg 2)),
    .mov .rax (.mem (sp sK)), .alu .add .rax (.imm 7), .shift .shr .rax 3, .mov .r10 (.mem (sp sScrLen)),
    .alu .sub .r10 (.reg .rax), .store (sp 8) .r10, .shift .shl .rax 3, .alu .add .rax (.reg .rcx),
    .store (sp 0) .rax, .mov .rcx (.mem (sp sBits))]

variable (chkN : String) (chkC : Prog isa) (pubN : String) (pubC : Prog isa)

def verifyCBody : Prog isa :=
  seqs [.block (verifyPrologue ++ n0),
    .ite .e verifyFail (seqs [.block (emBitsB ++ pubArgsC), .call pubN pubC, .block chkArgs, .call chkN chkC,
      .block [.alu .and .rax (.mem (sp sAcc))]]),
    .block restoreRegs]

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, calling `checkEncoding`. -/
def verifyC : Prog isa := .frame (.alloc frameBytes) (verifyCBody chkN chkC pubN pubC) (.free frameBytes)

end VG.Impl.RsaPss.X86_64
