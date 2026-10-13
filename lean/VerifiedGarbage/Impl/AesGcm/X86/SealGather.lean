module

public import VerifiedGarbage.Impl.AesGcm.X86

/-!
# AES-GCM one-shot encryption out of place, from a list of slices: x86 (32-bit) implementation

`vg_aes_gcm_seal_gather(ctx, rounds, nonce, nonce_len, aad, aad_len, src,
src_count, dst, len, tag)`, cdecl (every argument on the stack, at
`[esp + 4]` on entry), copies the slices `src` lists, one after the other,
to `dst`, and encrypts them there in place with a call of
`vg_aes_gcm_seal(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len, tag)`
(`name`, `code`: an instance of it).

It allocates a frame of 48 bytes: the call's nine arguments at `esp` …
`esp + 32`, and our caller's `ebx`, `esi` and `edi`, which the copy uses, at
`esp + 36` … `esp + 44`; our arguments are then at `esp + 52` … `esp + 92`.
The copy has `esi` at the next descriptor, `ebx` the number of slices left
and `edx` where the next slice goes; each slice is copied from `edi` a word
at a time through `eax`, with `ecx` its number of words (`copyWords`), then
its last `len mod 4` bytes one at a time (`copyLoop`). The branches are on
`src_count` and the slices' lengths alone.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86.SealGather

open VG.X86

/-- `[esp + d]`. -/
def sp (d : Nat) : MemOp := at_ .esp d

/-- Our caller's `ebx`, `esi` and `edi` kept in the frame; the call's
arguments `ctx`, `rounds`, `nonce`, `nonce_len`, `aad`, `aad_len`, `dst`,
`len` and `tag` laid out in it; and the copy's registers: `src` in `esi`,
`src_count` in `ebx` and `dst` in `edx`. -/
def entry : List Instr :=
  [.store (sp 36) .ebx, .store (sp 40) .esi, .store (sp 44) .edi,
    .mov .eax (.mem (sp 52)), .store (sp 0) .eax, .mov .eax (.mem (sp 56)), .store (sp 4) .eax,
    .mov .eax (.mem (sp 60)), .store (sp 8) .eax, .mov .eax (.mem (sp 64)), .store (sp 12) .eax,
    .mov .eax (.mem (sp 68)), .store (sp 16) .eax, .mov .eax (.mem (sp 72)), .store (sp 20) .eax,
    .mov .eax (.mem (sp 84)), .store (sp 24) .eax, .mov .eax (.mem (sp 88)), .store (sp 28) .eax,
    .mov .eax (.mem (sp 92)), .store (sp 32) .eax,
    .mov .esi (.mem (sp 76)), .mov .ebx (.mem (sp 80)), .mov .edx (.mem (sp 84))]

/-- Copies the `ecx` (at least 1) words at `edi` to `edx`, through `eax`. -/
def copyWords : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .edi 0)), .store (at_ .edx 0) .eax, .alu .add .edi (imm 4),
    .alu .add .edx (imm 4), .alu .sub .ecx (imm 1)]) .ne

/-- The slice's address and its number of whole words. -/
def wordsArg : List Instr :=
  [.mov .edi (.mem (at_ .esi 0)), .mov .ecx (.mem (at_ .esi 4)), .shift .shr .ecx 2, .alu .cmp .ecx (imm 0)]

/-- Its number of last bytes, the length (from the descriptor) modulo 4. -/
def bytesArg : List Instr := [.mov .ecx (.mem (at_ .esi 4)), .alu .and .ecx (imm 3)]

/-- Copies the slice that the descriptor at `esi` lists to `edx`, advancing
`edx` past it. -/
def copySlice : Prog isa :=
  .seq (.block wordsArg)
  (.seq (.ite .e (.block []) copyWords)
  (.seq (.block bytesArg)
    (.ite .e (.block []) copyLoop)))

/-- The next descriptor, and one slice fewer. -/
def next : List Instr := [.alu .add .esi (imm 8), .alu .sub .ebx (imm 1)]

/-- Copies the `ebx` (at least 1) slices that the descriptors at `esi` list
to `edx`, one after the other. -/
def gatherLoop : Prog isa := .loop (.seq copySlice (.block next)) .ne

/-- Copies the `ebx` slices that the descriptors at `esi` list to `edx`. -/
def gather : Prog isa := .seq (.block [.alu .cmp .ebx (imm 0)]) (.ite .e (.block []) gatherLoop)

/-- Our caller's `ebx`, `esi` and `edi` back from the frame. -/
def restore : List Instr := [.mov .ebx (.mem (sp 36)), .mov .esi (.mem (sp 40)), .mov .edi (.mem (sp 44))]

/-- `vg_aes_gcm_seal_gather`, calling `vg_aes_gcm_seal` (`name`, `code`). -/
def sealGather (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc 48)
    (.seq (.block entry)
    (.seq gather
    (.seq (.call name code)
      (.block restore))))
    (.free 48)

end VG.Impl.AesGcm.X86.SealGather
