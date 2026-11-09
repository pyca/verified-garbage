module

public import VerifiedGarbage.Impl.AesXts.X86_64Unit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

/-!
# XTS-AES of whole data units, out of place: x86-64 implementation

`vg_aes_xts_encrypt_unit_to(schedule = rdi, tweak_schedule = rsi, rounds = rdx, i = rcx, src = r8,
len = r9, dst = [rsp + 8], dst_len = [rsp + 16], scratch = [rsp + 24])` and
`vg_aes_xts_decrypt_unit_to` with the same arguments (see
`VG.Spec.Xts.aesEncryptUnitToContract` and `aesDecryptUnitToContract`): the
functions of `X86_64Unit.lean` with the data unit read from `src` and
written to `dst`. They are generic over the in-place whole-block functions
(`Xts`, for the tweak and ciphertext stealing) and the out-of-place ones
(`XtsTo`, `vg_aes_xts_encrypt_to` and `vg_aes_xts_decrypt_to`: `src` in
`rcx`, `dst` in `r10`, the other arguments those of the in-place ones).

The scratch buffer and the registers kept across the calls are those of
`X86_64Unit.lean`, with `dst` in `r12` and `src` in `r14`:

* the tweak `T = AES-enc(Key2, i)`, as in place;
* the whole blocks before the last bytes, `h` of them (all `m = len / 16`
  for encryption, or for decryption without a partial block; `m - 1`
  otherwise), from `src` to `dst` by one call of the out-of-place function
  from `T` (`argsTo`);
* the `len - 16 h` bytes after them, fewer than 32, copied from `src` to
  `dst` (`copyRest`, with `copyBytes`);
* ciphertext stealing on `dst` as in place, which then holds the data unit
  as the in-place function would have left it.

Only the pointers, `rounds` and `len` can affect timing: the branches are on
`len`.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86_64UnitTo

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesXts.X86_64Unit (Xts at_ tO zO save restore tweakIn split encSteal nextT lastAddr argsL
  stealPre swap)

/-- An implementation of `vg_aes_xts_encrypt_to` and `vg_aes_xts_decrypt_to`
to call: their symbols and code. -/
structure XtsTo where
  enc : Blocks
  dec : Blocks

/-- The scratch buffer (the third stack argument) into `rax`. -/
def ldS : List Instr := [.mov .rax (.mem (at_ .rsp 24))]

/-- The arguments to the registers kept across the calls: `dst` (the first
stack argument) in `r12` and `src` in `r14`. -/
def setup : List Instr :=
  [.mov .r15 (.reg .rax), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx), .mov .r12 (.mem (at_ .rsp 8)),
   .mov .r13 (.reg .r9), .mov .r14 (.reg .r8)]

def pro : List Instr := save ++ setup ++ tweakIn

/-- The tweak, `T = AES-enc(Key2, i)`. -/
def tweak (f : Blocks) : Prog isa := .seq (.block ldS) (.seq (.block pro) (.call f.name f.code))

/-- The arguments of an out-of-place call on the `len / 16` whole blocks
from the tweak. -/
def argsAll : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (.imm (BitVec.ofNat 32 tO)),
   .mov .rcx (.reg .r14), .mov .r8 (.reg .r13), .shift .shr .r8 4, .mov .r9 (.reg .r15), .mov .r10 (.reg .r12)]

/-- The arguments of an out-of-place call on all but the last whole block. -/
def argsHead : List Instr := argsAll ++ [.alu .sub .r8 (.imm 1)]

/-- The bytes after the first `h` whole blocks, `16 h` of them in `rax`,
copied from `src` to `dst`. -/
def copyRest : Prog isa :=
  .seq (.block [.mov .rsi (.reg .r14), .alu .add .rsi (.reg .rax), .mov .rdi (.reg .r12), .alu .add .rdi (.reg .rax),
      .mov .rcx (.reg .r13), .alu .sub .rcx (.reg .rax)])
    (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes .x16)

/-- `16 h` in `rax` for `h = len / 16`. -/
def wholeBytes : List Instr := [.mov .rax (.reg .r13), .shift .shr .rax 4, .shift .shl .rax 4]

/-- `16 h` in `rax` for `h = len / 16 - 1`. -/
def headBytes : List Instr := wholeBytes ++ [.alu .sub .rax (.imm 16)]

def encrypt (x : Xts) (y : XtsTo) : Prog isa :=
  .seq (tweak x.enc) (.seq (.block argsAll) (.seq (.call y.enc.name y.enc.code)
    (.seq (.seq (.block wholeBytes) copyRest)
      (.seq (.block split) (.seq (.ite .e (.block []) (encSteal x.enc)) (.block restore))))))

/-- The decryption of a data unit with a partial block, after the first
`m - 1` whole blocks and the bytes after them are at `dst`: as in place. -/
def decStealTail (f : Blocks) : Prog isa :=
  .seq (.block (nextT ++ split ++ lastAddr ++ argsL zO)) (.seq (.call f.name f.code)
    (.seq (.block (split ++ stealPre)) (.seq swap (.seq (.block (argsL tO)) (.call f.name f.code)))))

def decrypt (x : Xts) (y : XtsTo) : Prog isa :=
  .seq (tweak x.enc) (.seq (.block split)
    (.seq (.ite .e (.seq (.block argsAll) (.call y.dec.name y.dec.code))
      (.seq (.block argsHead) (.seq (.call y.dec.name y.dec.code)
        (.seq (.seq (.block headBytes) copyRest) (decStealTail x.dec)))))
      (.block restore)))

end VG.Impl.AesXts.X86_64UnitTo
