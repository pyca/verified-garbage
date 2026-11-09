module

public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

/-!
# AES-GCM decryption out of place, by a copy: x86-64 implementation

`vg_aes_gcm_open_to(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx,
aad = r8, aad_len = r9, src = [rsp + 8], len = [rsp + 16], dst = [rsp + 24],
dst_len = [rsp + 32], tag = [rsp + 40], tag_len = [rsp + 48])`, for an
instance of `vg_aes_gcm_open` (`f`) of any key context: the `len` bytes at
`src` are copied to `dst` (`copyBytes`, as wide as the CPUs of the instance
called allow: `w`, 16 bytes at a time with SSE2's `movdqu` or 32 with AVX's
`vmovdqu`), and decrypted there in place by a call of
`f(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len, tag, tag_len)`.
If it returns 0 (the tag is wrong), `dst` holds the ciphertext again, and
is zeroed a byte at a time (`wipe`), with `rax` zeroed first, so that the
result is still 0.

Its frame pushes eleven words: the six argument registers, which wait there
for the call, and five more, the lowest four of which become the call's
stack arguments (`dst`, `len`, `tag`, `tag_len`), so that the stack pointer
is a multiple of 16 at the call. Our stack arguments are then at
`rsp + 96` … `rsp + 136`.

Only the pointers, the lengths, `rounds` and whether `f` returns 1 or 0 can
affect timing.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.OpenTo

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm dstB Fn)

/-- The registers the frame pushes: the six argument registers, then five
words for the call's stack arguments. -/
abbrev frameRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rax, .rax, .rax, .rax, .rax]

/-- The copy's arguments: `src` in `rsi`, `dst` in `rdi` and `len` in
`rcx`. -/
def entry : List Instr :=
  [.mov .rsi (.mem (at_ .rsp 96)), .mov .rdi (.mem (at_ .rsp 112)), .mov .rcx (.mem (at_ .rsp 104))]

/-- The six argument registers back from the frame. -/
def callRegs : List Instr :=
  [.mov .rdi (.mem (at_ .rsp 80)), .mov .rsi (.mem (at_ .rsp 72)), .mov .rdx (.mem (at_ .rsp 64)),
   .mov .rcx (.mem (at_ .rsp 56)), .mov .r8 (.mem (at_ .rsp 48)), .mov .r9 (.mem (at_ .rsp 40))]

/-- The word at `rsp + src` into `rsp + d`, through `rax`. -/
def stArg (d src : Nat) : List Instr := [.mov .rax (.mem (at_ .rsp src)), .store (at_ .rsp d) .rax]

/-- The call's arguments: the six argument registers back from the frame,
then `dst`, `len`, `tag` and `tag_len` into its lowest four words. -/
def callArgs : Prog isa :=
  .seq (.block callRegs)
    (.seq (.block (stArg 0 112)) (.seq (.block (stArg 8 104)) (.seq (.block (stArg 16 128)) (.block (stArg 24 136)))))

/-- `dst` in `rdi`, `len` in `rcx`, `rax` and the index `r10` zeroed, and
`cmp r10, rcx`. -/
def wipeArgs : List Instr :=
  [.mov .rdi (.mem (at_ .rsp 112)), .mov .rcx (.mem (at_ .rsp 104)), .mov32 .rax (imm 0),
   .mov32 .r10 (imm 0), .alu .cmp .r10 (.reg .rcx)]

/-- One byte of `dst` zeroed (`al` is 0). -/
def wipeBody : List Instr :=
  [.store8 dstB .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)]

/-- The `len` bytes at `dst` zeroed, one at a time, and `rax` zeroed. -/
def wipe : Prog isa :=
  .seq (.block wipeArgs) (.ite .e (.block []) (.loop (.block wipeBody) .ne))

/-- After the call: `dst` wiped if it returned 0. -/
def after : Prog isa :=
  .seq (.block [.alu32 .test .rax (.reg .rax)]) (.ite .e wipe (.block []))

/-- `vg_aes_gcm_open_to`, copying `2 ^ w.log` bytes at a time and calling
the instance `f` of `vg_aes_gcm_open`. -/
def openTo (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width) (f : Fn) : Prog isa :=
  .frame (.push frameRegs)
    (.seq (.block entry)
    (.seq (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes w)
    (.seq callArgs
    (.seq (.call f.name f.code) after))))
    (.pop .r11 11)

end VG.Impl.AesGcm.X86_64.OpenTo
