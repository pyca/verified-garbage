module

public import VerifiedGarbage.Impl.RsaOaep.X86_64

/-!
# RSASSA-PSS (RFC 8017 §8.1, EMSA-PSS §9.1) on x86-64

`sign` and `verify` (with a precomputed public key), for the hash function
`H` (the digest's) and MGF1's hash function `G` that the selectors `hash`
and `mgf1_hash` name (MD5, SHA-1 or a SHA-2 function), calling their
streaming functions through the tables `hash_fns` and `mgf1_fns`
(`Spec/HashFns.lean`), MGF1 (`Impl/Mgf1/X86_64.lean`), and the RSA
operation: the private-key operation checked against `e`
(`vg_rsa_private_checked`) when signing, the precomputed public-key
operation within BoringSSL's limits (`vg_rsa_public_precomputed_checked`)
when verifying.

The code runs in RSAES-OAEP's frame and working space
(`Impl/RsaOaep/X86_64.lean`), whose slots, offsets, MGF1 layout, selector
prologue and shift it shares: the slots of its own are those RSAES-OAEP
uses for other values. `selPrologueWith pssLens` stores `hLen` (`sHD`) and
the other lengths of `H`, MGF1's `hLen` (`sGD`), and the tables' words.

## The encoding's parameters

From `n`'s first byte `n₀`: `n₀ = 0` makes the modulus invalid (both
operations refuse it); otherwise `v = smear(n₀ >> 1)` (every bit below the
top one of `n₀ >> 1`, by three shifts and ORs) is `0xFF >> z` for
`z = 8 emLen - emBits`, unless it is zero (`n₀ = 1`), in which case
`emLen = k - 1` (`lo = 1`) and the mask is `0xFF`.

## Signing

The checks (`n₀ ≠ 0`, `emLen ≥ hLen + 2`, `emLen - hLen - 2 ≥ sLen`) fail
with zeros to `out` and 0. Then `H = Hash(0⁸ ‖ mHash ‖ salt)` (the prefix
`0⁸ ‖ mHash` written to `scratch + oMp`, the salt hashed where it is),
`EM = 0^lo ‖ 0…0 ‖ 0x01 ‖ salt ‖ H ‖ 0xbc` is written to `scratch + oEm`;
MGF1 masks `DB`; its top bits are cleared; and `vg_rsa_private_checked` is
called on it, whose result is ours.

## Verifying

The public checks return 0. Then the public operation writes the
signature's RSAVP1 (or zeros) to `scratch + oEm`, and an accumulator `acc`
ORs together every value that is nonzero exactly when a check fails (the
leading zero byte, `0xbc`, the top bits of `maskedDB`); MGF1 unmasks `DB`;
the first nonzero byte of `DB` is found by masks over all of it
(`posScan`), and must be `0x01`, with the salt after it of the expected
length if one is (`posCheck`). With the salt length given (`any_salt_len`
zero), the salt is at a public offset, and `H' = Hash(0⁸ ‖ mHash ‖ salt)` is
hashed there (`fixedBack`). Otherwise its length `L` is secret: `DB` is
copied to the buffer `scratch + oBuf` and shifted left by `pos + 1` bytes,
leaving the salt and zeros; the prefix is hashed, and for every candidate
length `c < dbLen` a copy of the state is finalized, its digest selected
under the mask of `c = L`, and the state updated with the buffer's byte `c`
(`autoBack`). `H'` is compared with `H`, and the result is 1 if `acc = 0`,
computed without a branch.
-/

@[expose] public section

namespace VG.Impl.RsaPss.X86_64

open VG.X86_64
open VG.Impl.Mgf1.X86_64 (seqs sp ix at_ step byteLoop mgfXor initF updF finF)
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sSrc sSrcLen sDst sDstLen sCtr sOut sN sK sE sEl
  sScrLen sIdx sA sHD sFnH oEm oBuf oSt oDig oLh oW oRsa lay arg scr argSlot im selPrologueWith zeroOut
  clearEm shift)

/-! ## The slots of PSS's own, and its offsets in `scratch` -/

/-- The digest's address. -/
def sDig : Nat := 216
/-- Signing: the salt's address and length. -/
def sSalt : Nat := 224
def sSaltLen : Nat := 232
/-- Verifying: the signature's address, whether any salt length is
accepted, and the expected salt length. -/
def sSig : Nat := 168
def sAny : Nat := 224
def sSlen : Nat := 232
/-- The mask of `DB`'s first byte, and `lo`. -/
def sC : Nat := 240
def sLo : Nat := 248
/-- `DB`'s address and `dbLen`. -/
def sEb : Nat := 264
def sDb : Nat := 352
/-- Verifying: the accumulator, and the salt's length found, in the words
of the frame that the private-key operation's stack arguments use when
signing (the public one's are the first four). -/
def sAcc : Nat := 32
def sL : Nat := 40

/-- The prefix `0⁸ ‖ mHash` of `M'`: 72 bytes. -/
def oMp : Nat := 3584
/-- A copy of the streaming state: 256 bytes. -/
def oSt2 : Nat := 3712

/-- The hash functions' numbers and digest lengths: MD5 (0), SHA-1 (1) and
the SHA-2 functions (2 to 7), as `Spec.HashId.mgf1` numbers them. -/
def pssLens : List (Nat × Nat) :=
  [(0, 16), (1, 20), (2, 28), (3, 32), (4, 48), (5, 64), (6, 28), (7, 32)]

/-! ## The encoding's parameters -/

/-- `n₀`, and ZF set if it is zero. -/
def n0 : List Instr := [.mov .rsi (.mem (sp sN)), .movzx8 .rax (at_ .rsi), .alu .test .rax (.reg .rax)]

/-- `rdx := smear(n₀ >> 1)`, ZF set if zero. -/
def smear : List Instr :=
  [.mov .rdx (.reg .rax), .shift .shr .rdx 1, .mov .rax (.reg .rdx), .shift .shr .rax 1, .alu .or .rdx (.reg .rax),
    .mov .rax (.reg .rdx), .shift .shr .rax 2, .alu .or .rdx (.reg .rax), .mov .rax (.reg .rdx),
    .shift .shr .rax 4, .alu .or .rdx (.reg .rax), .alu .test .rdx (.reg .rdx)]

/-- The mask `sC` and `lo` (`sLo`); `rax := emLen = k - lo`, and CF set
if `emLen < hLen + 2`. -/
def emLen : Prog isa :=
  .seq (.ite .e (.block [.mov32 .rdx (.imm 0xFF), .mov32 .r8 (.imm 1)]) (.block [.mov32 .r8 (.imm 0)]))
    (.block [.store (sp sC) .rdx, .store (sp sLo) .r8, .mov .rax (.mem (sp sK)), .alu .sub .rax (.reg .r8),
      .mov .r9 (.mem (sp sHD)), .alu .add .r9 (.imm 2), .alu .cmp .rax (.reg .r9)])

/-- `rax := emLen - hLen - 2`, the longest salt, and CF set if it is less
than the salt's length in `rdx`. -/
def saltFits : List Instr :=
  [.alu .sub .rax (.mem (sp sHD)), .alu .sub .rax (.imm 2), .alu .cmp .rax (.reg .rdx)]

/-- `dbLen = emLen - hLen - 1` (from `rax = emLen - hLen - 2`) and
`DB = scratch + oEm + lo` into their slots. -/
def dbSlots : List Instr :=
  ([.alu .add .rax (.imm 1), .store (sp sDb) .rax] : List Instr) ++ scr .rax oEm ++
    ([.mov .rdx (.mem (sp sLo)), .alu .add .rax (.reg .rdx), .store (sp sEb) .rax] : List Instr)

/-! ## Common pieces -/

/-- The prefix `0⁸ ‖ mHash` to `scratch + oMp`: the digest after its first
8 bytes, then those cleared. -/
def mPrefix : Prog isa :=
  seqs [.block ([.mov .rsi (.mem (sp sDig)), .mov .r10 (.mem (sp sHD)), .mov32 .r8 (.imm 0)] ++ scr .rcx oMp),
    byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8 8) .rax] (.reg .r10),
    .block [.mov32 .rax (.imm 0), .store (at_ .rcx) .rax]]

/-- `H`'s `init` on the state, and `update` of it with the prefix. -/
def hashPrefix : Prog isa :=
  seqs [.block (scr .rdi oSt), initF sFnH,
    .block (scr .rdi oSt ++ [.mov32 .rsi (.imm 0)] ++ scr .rdx oMp ++
      [.mov .rcx (.mem (sp sHD)), .alu .add .rcx (.imm 8)] ++ scr .r8 oW),
    updF sFnH]

/-- `rsi := hLen + 8`, the prefix's length. -/
def plen : List Instr := [.mov .rsi (.mem (sp sHD)), .alu .add .rsi (.imm 8)]

/-- MGF1's slots for masking `DB` (`dbLen` bytes at `DB`) with `H` (`hLen`
bytes after it). -/
def mgfArgs : List Instr :=
  [.mov .rax (.mem (sp sEb)), .mov .rdx (.mem (sp sDb)), .mov .r9 (.mem (sp sHD)), .mov .rcx (.reg .rax),
    .alu .add .rcx (.reg .rdx), .store (sp sDst) .rax, .store (sp sDstLen) .rdx, .store (sp sSrc) .rcx,
    .store (sp sSrcLen) .r9]

/-- `DB`'s first byte ANDed with the mask `0xFF >> z` (`sC`). -/
def clearTop : List Instr :=
  [.mov .rdi (.mem (sp sEb)), .movzx8 .rax (at_ .rdi), .alu .and .rax (.mem (sp sC)), .store8 (at_ .rdi) .rax]

/-! ## Signing

`sign(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8, e_len = r9,
p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, digest,
digest_len, salt, salt_len, scratch, scratch_len, hash, mgf1_hash,
hash_fns, mgf1_fns)`, the last twenty on the stack. -/

/-- The arguments into their slots. -/
def signPrologue : List Instr :=
  [.store (sp sOut) .rdi, .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8, .store (sp sEl) .r9] ++
  argSlot 10 sDig ++ argSlot 12 sSalt ++ argSlot 13 sSaltLen ++ argSlot 14 sScr ++ argSlot 15 sScrLen

/-- Zeros to `out`, and 0. -/
def signFail : Prog isa := zeroOut

/-- `H = Hash(0⁸ ‖ mHash ‖ salt)` to `scratch + oDig`. -/
def hashM : Prog isa :=
  seqs [hashPrefix,
    .block (scr .rdi oSt ++ plen ++ [.mov .rdx (.mem (sp sSalt)), .mov .rcx (.mem (sp sSaltLen))] ++ scr .r8 oW),
    updF sFnH,
    .block (scr .rdi oSt ++ plen ++ [.alu .add .rsi (.mem (sp sSaltLen))] ++ scr .rdx oDig ++ scr .rcx oW),
    finF sFnH]

/-- `0x01` at `DB + dbLen - sLen - 1`, and the salt after it, if it is not
empty. -/
def putSalt : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax),
      .mov .rax (.mem (sp sSaltLen)), .alu .sub .rdi (.reg .rax), .alu .sub .rdi (.imm 1), .mov32 .rax (.imm 1),
      .store8 (at_ .rdi) .rax])
    (.seq (.block [.mov .rsi (.mem (sp sSalt)), .mov .r10 (.mem (sp sSaltLen)), .mov32 .r8 (.imm 0),
        .alu .test .r10 (.reg .r10)])
      (.ite .e (.block []) (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8 1) .rax] (.reg .r10))))

/-- `H` (the digest) at `DB + dbLen`, and `0xbc` at `EM`'s last byte. -/
def putH : Prog isa :=
  .seq (.block ([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] ++
      scr .rsi oDig ++ [.mov .r10 (.mem (sp sHD)), .mov32 .r8 (.imm 0)]))
    (.seq (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.reg .r10))
      (.block (scr .rdi oEm ++ [.mov .rax (.mem (sp sK)), .alu .add .rdi (.reg .rax), .alu .sub .rdi (.imm 1),
        .mov32 .rax (.imm 0xbc), .store8 (at_ .rdi) .rax])))

/-- The arguments of `vg_rsa_private_checked`: `out`, `n` (`k` bytes), `e`,
`EM` as the input (`k` bytes), the private key, and the rest of `scratch`. -/
def privArgs : List Instr :=
  (List.range 10).flatMap (fun j => [.mov .rax (.mem (arg j)), .store (sp (16 + 8 * j)) .rax]) ++
  scr .rax oEm ++ [.store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] ++
  scr .rax oRsa ++ [.store (sp 96) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 104) .rax] ++
  [.mov .rdi (.mem (sp sOut)), .mov .rsi (.mem (sp sK)), .mov .rdx (.mem (sp sN)), .mov .rcx (.mem (sp sK)),
    .mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))]

/-- After the checks: `EM` at `scratch + oEm`. -/
def signEnc : Prog isa :=
  seqs [.block dbSlots, clearEm, mPrefix, hashM, putSalt, putH, .block mgfArgs, mgfXor lay, .block clearTop]

variable (privN : String) (privC : Prog isa)

/-- After the checks: the encoding, and the private-key operation. -/
def signMain : Prog isa := seqs [signEnc, .block privArgs, .call privN privC]

/-- The prologue, the selectors and the tables (the stack arguments 16 to
19), the checks, then `signMain`. -/
def signBody : Prog isa :=
  seqs [.block signPrologue, selPrologueWith pssLens 16 17, .block n0,
    .ite .e signFail (seqs [.block smear, emLen,
      .ite .b signFail (seqs [.block ([.mov .rdx (.mem (sp sSaltLen))] ++ saltFits),
        .ite .b signFail (signMain privN privC)])])]

/-- `vg_rsa_pss_sign`. -/
def sign : Prog isa := .frame (.alloc frameBytes) (signBody privN privC) (.free frameBytes)

/-! ## Verifying

`verify(n = rdi, n_len = rsi, e = rdx, e_len = rcx, digest = r8,
digest_len = r9, sig, sig_len, any_salt_len, salt_len, scratch,
scratch_len, pre, pre_len, hash, mgf1_hash, hash_fns, mgf1_fns)`, the last
twelve on the stack. -/

def verifyPrologue : List Instr :=
  [.store (sp sN) .rdi, .store (sp sK) .rsi, .store (sp sE) .rdx, .store (sp sEl) .rcx, .store (sp sDig) .r8] ++
  argSlot 0 sSig ++ argSlot 4 sScr ++ argSlot 5 sScrLen

/-- `sAny := any_salt_len ≠ 0` and `sSlen := salt_len`; `rdx` the expected
length for the check, 0 if any. -/
def anyArgs : Prog isa :=
  .seq (.block [.mov .rax (.mem (arg 3)), .store (sp sSlen) .rax, .mov32 .rax (.mem (arg 2)),
      .alu .test .rax (.reg .rax)])
    (.ite .e (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))])
      (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]))

/-- 0 returned. -/
def verifyFail : Prog isa := .block [.mov32 .rax (.imm 0)]

/-- The arguments of the public operation: `EM`'s place (`k` bytes), the
cached values `pre`, `e`, the signature (`k` bytes), and the rest of
`scratch`. -/
def pubArgs : List Instr :=
  [.mov .rax (.mem (sp sSig)), .store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] ++
  scr .rax oRsa ++ [.store (sp 16) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 24) .rax] ++ scr .rdi oEm ++
  [.mov .rsi (.mem (sp sK)), .mov .rdx (.mem (arg 6)), .mov .rcx (.mem (arg 7)), .mov .r8 (.mem (sp sE)),
    .mov .r9 (.mem (sp sEl))]

/-- `acc :=` the leading byte if `lo = 1`, `EM`'s last byte `⊕ 0xbc`, and the
top bits of `maskedDB`'s first byte. -/
def acc0 : List Instr :=
  scr .rcx oEm ++ [.mov .rdi (.mem (sp sK)), .alu .add .rdi (.reg .rcx), .alu .sub .rdi (.imm 1),
    .movzx8 .rax (at_ .rdi), .alu .xor .rax (.imm 0xbc),
    .movzx8 .r9 (at_ .rcx), .mov .r10 (.mem (sp sLo)), .mov32 .r11 (.imm 0), .alu .sub .r11 (.reg .r10),
    .alu .and .r9 (.reg .r11),
    .alu .or .rax (.reg .r9),
    .mov .rdi (.mem (sp sEb)), .movzx8 .r9 (at_ .rdi), .mov .r11 (.mem (sp sC)), .alu .xor .r11 (.imm 0xFF),
    .alu .and .r9 (.reg .r11), .alu .or .rax (.reg .r9), .store (sp sAcc) .rax]

/-- The first nonzero byte of `DB`: its index into `rsi`, its value into
`r11`, and `rdx` all ones if there is one. -/
def posScan : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp sEb)), .mov .r10 (.mem (sp sDb)), .mov32 .r8 (.imm 0), .mov32 .rdx (.imm 0),
      .mov32 .rsi (.imm 0), .mov32 .r11 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rdi .r8), .mov .r9 (.reg .rax), .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9),
      .alu .xor .r9 (.imm 0xFFFFFFFF), .mov .rcx (.reg .rdx), .alu .xor .rcx (.imm 0xFFFFFFFF),
      .alu .and .r9 (.reg .rcx), .mov .rcx (.reg .r8), .alu .and .rcx (.reg .r9), .alu .or .rsi (.reg .rcx),
      .alu .and .rax (.reg .r9), .alu .or .r11 (.reg .rax), .alu .or .rdx (.reg .r9)] (.reg .r10))

/-- `acc |= (val ⊕ 1) | ¬found`, the salt's length `L = dbLen - pos - 1`
compared with the expected one if there is one, `pos` and `L` into their
slots. -/
def posCheck : Prog isa :=
  .seq (.block [.alu .xor .r11 (.imm 1), .alu .xor .rdx (.imm 0xFFFFFFFF), .alu .or .r11 (.reg .rdx),
      .mov .rax (.mem (sp sAcc)), .alu .or .rax (.reg .r11), .store (sp sIdx) .rsi,
      .mov .rcx (.mem (sp sDb)), .alu .sub .rcx (.reg .rsi), .alu .sub .rcx (.imm 1),
      .mov .r9 (.mem (sp sAny)), .alu .test .r9 (.reg .r9)])
    (.seq (.ite .e (.block [.mov .r9 (.reg .rcx), .alu .xor .r9 (.mem (sp sSlen)), .alu .or .rax (.reg .r9)])
        (.block []))
      (.block [.store (sp sAcc) .rax, .store (sp sL) .rcx]))

/-- `acc` ORed with `H' ⊕ H` (`H'` at `scratch + oDig`), and the result: 1
if `acc = 0`. -/
def cmpH : Prog isa :=
  .seq (.block (scr .rcx oDig ++ [.mov .rdi (.mem (sp sEb)), .mov .rdx (.mem (sp sDb)), .alu .add .rdi (.reg .rdx),
      .mov .r10 (.mem (sp sHD)), .mov .rdx (.mem (sp sAcc)), .mov32 .r8 (.imm 0)]))
    (.seq (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .r9 (ix .rdi .r8), .alu .xor .rax (.reg .r9),
        .alu .or .rdx (.reg .rax)] (.reg .r10))
      (.block [.alu .cmp .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 1)]))

/-- With the salt's length given: `H' = Hash(0⁸ ‖ mHash ‖ salt)`, the salt
the last `sLen` bytes of `DB`. -/
def fixedBack : Prog isa :=
  seqs [mPrefix, hashPrefix,
    .block (scr .rdi oSt ++ plen ++ [.mov .rdx (.mem (sp sEb)), .alu .add .rdx (.mem (sp sDb)),
      .alu .sub .rdx (.mem (sp sSlen)), .mov .rcx (.mem (sp sSlen))] ++ scr .r8 oW),
    updF sFnH,
    .block (scr .rdi oSt ++ plen ++ [.alu .add .rsi (.mem (sp sSlen))] ++ scr .rdx oDig ++ scr .rcx oW),
    finF sFnH, cmpH]

/-- The buffer's 2048 bytes cleared, then `DB` copied to it, and `rcx` the
buffer for `shift`. -/
def copyDb : Prog isa :=
  seqs [.block (scr .rcx oBuf ++ [.mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)]),
    .loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8), .alu .cmp .r8 (.imm 2048)]) .ne,
    .block [.mov .rsi (.mem (sp sEb)), .mov .r10 (.mem (sp sDb)), .mov32 .r8 (.imm 0)],
    byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8) .rax] (.reg .r10)]

/-- The 256 bytes at `scratch + a` copied to `scratch + b`, a word at a
time: the streaming state, saved and restored. -/
def copyQ (a b : Nat) : Prog isa :=
  .seq (.block (scr .rsi a ++ scr .rdi b ++ [.mov32 .r8 (.imm 0)]))
    (.loop (.block [.mov .rax (.mem (ix .rsi .r8)), .store (ix .rdi .r8) .rax, .alu .add .r8 (.imm 8),
      .alu .cmp .r8 (.imm 256)]) .ne)

/-- `finalize` of the state, after `hLen + 8 + c` bytes (`c` in `sCtr`), to
`scratch + oLh`. -/
def finCand : Prog isa :=
  .seq (.block (scr .rdi oSt ++ plen ++ [.alu .add .rsi (.mem (sp sCtr))] ++ scr .rdx oLh ++ scr .rcx oW))
    (finF sFnH)

/-- The 64 bytes at `scratch + oLh` to `scratch + oDig` under the mask of
`c = L`. -/
def selCand : Prog isa :=
  .seq (.block ([.mov .rax (.mem (sp sCtr)), .alu .xor .rax (.mem (sp sL)), .alu .cmp .rax (.imm 1),
      .alu .sbb .r11 (.reg .r11)] ++ scr .rcx oLh ++ scr .rdi oDig ++ [.mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdx (ix .rdi .r8), .alu .xor .rax (.reg .rdx),
      .alu .and .rax (.reg .r11), .alu .xor .rdx (.reg .rax), .store8 (ix .rdi .r8) .rdx] (.imm 64))

/-- `update` of the state with the buffer's byte `c`, after `hLen + 8 + c`
bytes. -/
def updCand : Prog isa :=
  .seq (.block (scr .rdi oSt ++ plen ++ [.alu .add .rsi (.mem (sp sCtr))] ++ scr .rdx oBuf ++
      [.alu .add .rdx (.mem (sp sCtr)), .mov32 .rcx (.imm 1)] ++ scr .r8 oW))
    (updF sFnH)

/-- The next candidate, and ZF set after the last (`c = dbLen`). -/
def nextCand : List Instr :=
  [.mov .rax (.mem (sp sCtr)), .alu .add .rax (.imm 1), .store (sp sCtr) .rax, .alu .cmp .rax (.mem (sp sDb))]

/-- One candidate `c`: the saved state restored and finalized, its digest
selected if `c = L`; the saved state restored again, updated with the
buffer's byte `c`, and saved. -/
def cand : Prog isa :=
  seqs [copyQ oSt2 oSt, finCand, selCand, copyQ oSt2 oSt, updCand, copyQ oSt oSt2, .block nextCand]

/-- With any salt length: `DB` shifted to the buffer's start, the prefix
hashed and the state saved, and the digest of the prefix and the buffer's
first `c` bytes for every candidate `c < dbLen`, selected for `c = L`. -/
def autoBack : Prog isa :=
  seqs [mPrefix, copyDb, shift, hashPrefix, copyQ oSt oSt2, .block [.mov32 .rax (.imm 0), .store (sp sCtr) .rax],
    .loop cand .ne, cmpH]

/-- The salt's hash, by its length given or found, and the comparison. -/
def saltBack : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)]) (.ite .e fixedBack autoBack)

variable (pubN : String) (pubC : Prog isa)

/-- After the public checks. -/
def verifyMain : Prog isa :=
  seqs [.block dbSlots, .block pubArgs, .call pubN pubC, .block acc0, .block mgfArgs, mgfXor lay,
    .block clearTop, posScan, posCheck, saltBack]

/-- The prologue, the selectors and the tables (the stack arguments 8 to
11), the checks, then `verifyMain`. -/
def verifyBody : Prog isa :=
  seqs [.block verifyPrologue, selPrologueWith pssLens 8 9, .block n0,
    .ite .e verifyFail (seqs [.block smear, emLen,
      .ite .b verifyFail (seqs [anyArgs, .block ([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)),
          .alu .sub .rax (.reg .r8)] ++ saltFits),
        .ite .b verifyFail (verifyMain pubN pubC)])])]

/-- `vg_rsa_pss_verify_precomputed`. -/
def verify : Prog isa := .frame (.alloc frameBytes) (verifyBody pubN pubC) (.free frameBytes)

end VG.Impl.RsaPss.X86_64
