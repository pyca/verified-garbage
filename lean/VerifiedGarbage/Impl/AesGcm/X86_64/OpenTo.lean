module

public import VerifiedGarbage.Impl.AesGcm.X86_64

/-!
# AES-GCM decryption out of place: the frame of `vg_aes_gcm_open_to`

`vg_aes_gcm_open_to(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx,
aad = r8, aad_len = r9, src = [rsp + 8], len = [rsp + 16], dst = [rsp + 24],
dst_len = [rsp + 32], tag = [rsp + 40], tag_len = [rsp + 48])` calls an
instance of `vg_aes_gcm_open_split` (`OpenToSplit.openToSplit`) from a frame
of eleven words: the six argument registers, which wait there for the call,
and five more, which hold the call's stack arguments (`stArg`), so that the
stack pointer is a multiple of 16 at the call. Our stack arguments are then
at `rsp + 96` … `rsp + 136`. If the call returns 0 (the tag is wrong), `dst`
is zeroed a byte at a time (`wipe`), with `rax` zeroed first, so that the
result is still 0 (`after`).

Only the pointers, the lengths, `rounds` and whether the call returns 1 or 0
can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.OpenTo

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm dstB)

/-- The registers the frame pushes: the six argument registers, then five
words for the call's stack arguments. -/
abbrev frameRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rax, .rax, .rax, .rax, .rax]

/-- The word at `rsp + src` into `rsp + d`, through `rax`. -/
def stArg (d src : Nat) : List Instr := [.mov .rax (.mem (at_ .rsp src)), .store (at_ .rsp d) .rax]

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

end VG.Impl.AesGcm.X86_64.OpenTo
