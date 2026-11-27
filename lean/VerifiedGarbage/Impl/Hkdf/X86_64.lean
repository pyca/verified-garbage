module

public import VerifiedGarbage.Impl.Mgf1.X86_64.Table

/-!
# HKDF (RFC 5869) on x86-64, with HMAC through a table

Three functions, each with HMAC over the hash function of the table `hmac`
of the interface `Hmac` (`Spec/HmacTable.lean`), whose functions they call
indirectly (the table's word `j` into `r11`, then `call r11`): HMAC's `init`
for a key of any length (word 0), the streaming `update` (word 1) and HMAC's
`finalize` (word 2), each with its working space in `r8`. The digest length
`D` and HMAC's block size `B` are the table's words of data 4 and 5, which
the code loads where it needs them: nothing in the code depends on the hash
function but those two words and the table's functions.

* `vg_hkdf_key(prk = rdi, prk_len = rsi, key = rdx, hmac = rcx)` (`key`):
  `init` with `PRK` as the key, into the states at `key` and `key + 192`,
  with its working space in the frame.
* `vg_hkdf_extract(salt = rdi, salt_len = rsi, ikm = rdx, ikm_len = rcx,
  prk = r8, prk_len = r9, hmac = [rsp + 8])` (`extract`): `init` with the
  salt as the key, into the inner and outer states in the frame; `update`
  with the input keying material; `finalize`, which writes `PRK` to `prk`.
* `vg_hkdf_expand(key = rdi, info = rsi, info_len = rdx, out = rcx,
  out_len = r8, hmac = r9)` (`expand`): unless `out_len` is 0, for each
  block `T(i)` (`block`): the inner state at `key` made the working state in
  the frame, by copying its first 64 bytes (`copyW`): the inner state holds
  a whole block of key, so its hash value, at most 64 bytes, is all of it
  that matters; `update` with `T(i - 1)` (the `r15` bytes at `T` in the
  frame: none for the first block, `D` after), then with `info`, then with
  the counter `i` (a byte, kept in `r14`); `finalize` with the outer state
  at `key + 192`, which writes `T(i)` to the frame; and its first
  `min(D, rem)` bytes, `rem` the bytes of `out` still to write (in `r12`),
  copied to `out` (in `rbp`) a byte at a time. `key` is only read.

Each runs in a frame (`alloc`) holding our caller's registers it uses, at
its start, and the working space of the functions it calls (`8 W` bytes for
`update` and `finalize`, `8 (W + S)` for `init`); our variables live in
callee-saved registers, which the functions we call keep. Every address
depends only on the pointers and `D`, and every branch only on lengths.
-/

@[expose] public section

namespace VG.Impl.Hkdf.X86_64

open VG.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ byteLoop seqs)
open VG.Impl.Mgf1.X86_64.Table (Fns)

/-- The working space the table's functions get: `init`'s for a key of any
length, the most (SHA-512's AVX2 variant's `W + S` words). -/
def work : Nat := 3104

/-- `d ← rsp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .rsp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- The indirect call of the table's function `j`, among `ts`, with the
table in `t`: its word `j` into `r11`, then `call r11`. -/
def tcall (t : Reg) (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (at_ t (8 * j)))]) (Code.icalls (.callr .r11) ts)

/-- `B`, the table's word of data 5, into `d`. -/
def ldB (t d : Reg) : Instr := .mov d (.mem (at_ t 40))

/-- `D`, the table's word of data 4, into `d`. -/
def ldD (t d : Reg) : Instr := .mov d (.mem (at_ t 32))

/-! ## Keying HMAC -/

/-- `key`'s frame: the working space. -/
def kFr : Nat := work

/-- `init`'s arguments: the states at `key` and `key + 192`, `PRK` as the
key, the working space; and its address, the table's word 0, in `r11`. -/
def keyArgs : List Instr :=
  [.mov .r11 (.reg .rcx), .mov .rcx (.reg .rsi), .mov .rsi (.reg .rdx),
    .alu .add .rsi (.imm (BitVec.ofNat 32 192)), .mov .rax (.reg .rdx), .mov .rdx (.reg .rdi),
    .mov .rdi (.reg .rax), .mov .r8 (.reg .rsp), .mov .r11 (.mem (at_ .r11 0))]

/-- The frame's body of `vg_hkdf_key`, whose table's `init` may be `f`'s. -/
def keyMain (f : Fns) : Prog isa := .seq (.block keyArgs) (Code.icalls (.callr .r11) f.init)

/-- `vg_hkdf_key`. -/
def key (f : Fns) : Prog isa := .frame (.alloc kFr) (keyMain f) (.free kFr)

/-! ## HKDF-Extract -/

/-! Where things are in `extract`'s frame: our caller's `rbx`, `rbp`, `r12`
and `r13`, then HMAC's inner and outer states (192 bytes each), then the
working space. -/
def xIn : Nat := 32
def xOut : Nat := 224
def xWork : Nat := 416
/-- `extract`'s frame's size. -/
def xFr : Nat := xWork + work

/-- `extract`'s prologue: our caller's registers saved; `ikm` and its length
in `rbx` and `rbp`, `prk` in `r12`, the table (the argument on the stack) in
`r13`; then `init`'s arguments: the salt as the key, the states, the working
space. -/
def extractPro : List Instr :=
  [.store (sp 0) .rbx, .store (sp 8) .rbp, .store (sp 16) .r12, .store (sp 24) .r13,
    .mov .rbx (.reg .rdx), .mov .rbp (.reg .rcx), .mov .r12 (.reg .r8), .mov .r13 (.mem (sp (xFr + 8))),
    .mov .rdx (.reg .rdi), .mov .rcx (.reg .rsi)] ++ fr .rdi xIn ++ fr .rsi xOut ++ fr .r8 xWork

/-- `update`'s arguments: the inner state, which holds `B` bytes, the input
keying material, the working space. -/
def extractUpd : List Instr :=
  fr .rdi xIn ++ [ldB .r13 .rsi, .mov .rdx (.reg .rbx), .mov .rcx (.reg .rbp)] ++ fr .r8 xWork

/-- `finalize`'s arguments: the states, the `B + ikm_len` bytes the inner one
holds, `prk`, the working space. -/
def extractFin : List Instr :=
  fr .rdi xIn ++ fr .rsi xOut ++ [ldB .r13 .rdx, .alu .add .rdx (.reg .rbp), .mov .rcx (.reg .r12)] ++
    fr .r8 xWork

/-- Our caller's registers restored. -/
def extractEpi : List Instr :=
  [.mov .rbx (.mem (sp 0)), .mov .rbp (.mem (sp 8)), .mov .r12 (.mem (sp 16)), .mov .r13 (.mem (sp 24))]

/-- The frame's body of `vg_hkdf_extract`, whose table's functions may be
`f`'s. -/
def extractMain (f : Fns) : Prog isa :=
  seqs [.block extractPro, tcall .r13 0 f.init, .block extractUpd, tcall .r13 1 f.upd, .block extractFin,
    tcall .r13 2 f.fin, .block extractEpi]

/-- `vg_hkdf_extract`. -/
def extract (f : Fns) : Prog isa := .frame (.alloc xFr) (extractMain f) (.free xFr)

/-! ## HKDF-Expand -/

/-! Where things are in `expand`'s frame: our caller's `rbx`, `rbp` and
`r12`–`r15`, `info` and its length, the working state (192 bytes), `T(i)`
(64 bytes), the counter's byte (in a word), then the working space of
`update` and `finalize`. -/
def eInfo : Nat := 48
def eInfoLen : Nat := 56
def eW : Nat := 64
def eT : Nat := 256
def eC : Nat := 320
def eWork : Nat := 328
/-- `expand`'s frame's size: the working space of `update` and `finalize`
is at most 1872 bytes. -/
def eFr : Nat := eWork + 1872

/-- `expand`'s prologue: our caller's registers saved; `info` and its length
in the frame; `key` in `rbx`, `out` in `rbp`, the bytes of `out` left in
`r12`, the table in `r13`, the counter `i = 1` in `r14` and the length of
`T(i - 1)` (none yet) in `r15`. -/
def expandPro : List Instr :=
  [.store (sp 0) .rbx, .store (sp 8) .rbp, .store (sp 16) .r12, .store (sp 24) .r13, .store (sp 32) .r14,
    .store (sp 40) .r15, .store (sp eInfo) .rsi, .store (sp eInfoLen) .rdx, .mov .rbx (.reg .rdi),
    .mov .rbp (.reg .rcx), .mov .r12 (.reg .r8), .mov .r13 (.reg .r9), .mov32 .r14 (.imm 1),
    .mov32 .r15 (.imm 0), .alu .test .r12 (.reg .r12)]

/-- The inner state's first 64 bytes at `key` to the working state, a word at
a time through `rax`. -/
def copyW : List Instr :=
  (List.range 8).flatMap fun j => [.mov .rax (.mem (at_ .rbx (8 * j))), .store (sp (eW + 8 * j)) .rax]

/-- `update`'s arguments for `T(i - 1)`: the working state, which holds `B`
bytes, the `r15` bytes at `T`, the working space. -/
def updT : List Instr :=
  fr .rdi eW ++ [ldB .r13 .rsi] ++ fr .rdx eT ++ [.mov .rcx (.reg .r15)] ++ fr .r8 eWork

/-- `update`'s arguments for `info`: the working state, which holds
`B + r15` bytes. -/
def updI : List Instr :=
  fr .rdi eW ++ [ldB .r13 .rsi, .alu .add .rsi (.reg .r15), .mov .rdx (.mem (sp eInfo)),
    .mov .rcx (.mem (sp eInfoLen))] ++ fr .r8 eWork

/-- The counter's byte stored; `update`'s arguments for it: the working
state, which holds `B + r15 + info_len` bytes, and the byte. -/
def updC : List Instr :=
  [.store8 (sp eC) .r14] ++ fr .rdi eW ++
    [ldB .r13 .rsi, .alu .add .rsi (.reg .r15), .alu .add .rsi (.mem (sp eInfoLen))] ++ fr .rdx eC ++
    [.mov32 .rcx (.imm 1)] ++ fr .r8 eWork

/-- `finalize`'s arguments: the working state, which holds
`B + r15 + info_len + 1` bytes, the outer state at `key + 192`, `T`, the
working space. -/
def finT : List Instr :=
  fr .rdi eW ++ [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 192)), ldB .r13 .rdx,
    .alu .add .rdx (.reg .r15), .alu .add .rdx (.mem (sp eInfoLen)), .alu .add .rdx (.imm 1)] ++ fr .rcx eT ++
    fr .r8 eWork

/-- The bytes of `T(i)` to copy, `min(D, rem)`, into `rax`: `D`, or `rem` if
it is less (both public). -/
def outLen : Prog isa :=
  .seq (.block [ldD .r13 .rax, .alu .cmp .r12 (.reg .rax)]) (.ite .b (.block [.mov .rax (.reg .r12)]) (.block []))

/-- `rax` bytes of `T(i)` to `out`, a byte at a time (`r8` counting). -/
def outCopy : Prog isa :=
  .seq (.block [.mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rdx (ix .rsp .r8 eT), .store8 (ix .rbp .r8) .rdx] (.reg .rax))

/-- After the copy: `out` past the bytes written, `rem` less them, `T(i)`'s
`D` bytes the next block's `T(i - 1)`, the next counter; whether bytes of
`out` are left. -/
def nextBlock : List Instr :=
  [.alu .add .rbp (.reg .rax), .alu .sub .r12 (.reg .rax), ldD .r13 .r15, .alu .add .r14 (.imm 1),
    .alu .test .r12 (.reg .r12)]

/-- One block `T(i)`, whose table's functions may be `f`'s. -/
def block (f : Fns) : Prog isa :=
  seqs [.block copyW, .seq (.block updT) (tcall .r13 1 f.upd), .seq (.block updI) (tcall .r13 1 f.upd),
    .seq (.block updC) (tcall .r13 1 f.upd), .seq (.block finT) (tcall .r13 2 f.fin), outLen, outCopy,
    .block nextBlock]

/-- Our caller's registers restored. -/
def expandEpi : List Instr :=
  [.mov .rbx (.mem (sp 0)), .mov .rbp (.mem (sp 8)), .mov .r12 (.mem (sp 16)), .mov .r13 (.mem (sp 24)),
    .mov .r14 (.mem (sp 32)), .mov .r15 (.mem (sp 40))]

/-- The frame's body of `vg_hkdf_expand`, whose table's functions may be
`f`'s: the blocks while bytes of `out` are left. -/
def expandMain (f : Fns) : Prog isa :=
  seqs [.block expandPro, .ite .ne (.loop (block f) .ne) (.block []), .block expandEpi]

/-- `vg_hkdf_expand`. -/
def expand (f : Fns) : Prog isa := .frame (.alloc eFr) (expandMain f) (.free eFr)

end VG.Impl.Hkdf.X86_64
