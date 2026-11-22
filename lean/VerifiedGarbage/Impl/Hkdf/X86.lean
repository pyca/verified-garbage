module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86

/-!
# HKDF (RFC 5869) on x86 (32-bit), with HMAC through a table

Three functions, every argument on the stack (cdecl), each with HMAC over
the hash function of the table `hmac` of the interface `Hmac`
(`Spec/HmacTable.lean`), whose functions they call indirectly (`tcall`: the
table's address, our last argument, into `ebx`, its word `j` into `ebx`,
then `call ebx` in a frame of the callee's arguments, pushed last to first):
HMAC's `init` for a key of any length (word 0), the streaming `update`
(word 1) and HMAC's `finalize` (word 2), each with its working space in the
frame. The digest length `D` and HMAC's block size `B` are the table's
words of data 4 and 5, which the code copies to the frame on entry where it
needs them: nothing in the code depends on the hash function but those two
words and the table's functions.

Each runs in a frame (`alloc`) holding, from `esp`, our caller's `ebx`,
`esi`, `edi` and `ebp` (`saveRegs`, which the argument registers of the
calls overwrite), then our variables, then the buffers of the functions we
call; our arguments stay where our caller put them, above the frame and the
return address (`argM`).

* `vg_hkdf_key(prk, prk_len, key, hmac)` (`key`): `init` with `PRK` as the
  key, into the states at `key` and `key + 192`, with its working space in
  the frame.
* `vg_hkdf_extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`
  (`extract`): `init` with the salt as the key, into the inner and outer
  states in the frame; `update` with the input keying material; `finalize`,
  which writes `PRK` to `prk`, with the count `B + ikm_len`.
* `vg_hkdf_expand(key, info, info_len, out, out_len, hmac)` (`expand`):
  unless `out_len` is 0, for each block `T(i)` (`block`): the inner state at
  `key`, its 192 bytes, copied to the working state in the frame (the byte
  loop, `cpLoop`); `update` with `T(i - 1)` (`tlen` bytes at `T` in the
  frame: none for the first block, `D` after), then with `info`, then with
  the counter `i` (a byte, stored from the frame's word); `finalize` with the
  outer state at `key + 192`, which writes `T(i)` to the frame; and its first
  `n = min(D, rem)` bytes, `rem` the bytes of `out` still to write, copied
  to `out` by the byte loop, which leaves `ebx` past them. `key` is only
  read.

Every address depends only on the pointers, `esp` and `D`, and every branch
only on lengths.
-/

@[expose] public section

namespace VG.Impl.Hkdf.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Impl.Ecdsa.Rfc6979.X86 (Fns init5 upd6 fin6)

/-- `[esp + d]`, in the frame or our arguments above it. -/
def sp (d : Nat) : MemOp := { base := .esp, disp := d }

/-- `d ← esp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .esp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- Our argument `i`, above a frame of `F` bytes and the return address. -/
def argM (F i : Nat) : Src := .mem (sp (F + 4 + 4 * i))

/-- Our caller's registers, where the frame keeps them. -/
def saved : List (Reg × Nat) := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

/-- Our caller's registers into the frame. -/
def saveRegs : List Instr := saved.map fun (r, d) => .store (sp d) r

/-- Our caller's registers back. -/
def restoreRegs : List Instr := saved.map fun (r, d) => .mov r (.mem (sp d))

/-- The frame's entry: our caller's registers saved, the table (our argument
`ti`, above a frame of `F` bytes) in `eax`. -/
def entry (F ti : Nat) : List Instr := saveRegs ++ [.mov .eax (argM F ti)]

/-- The indirect call of the table's function `j` (the table our argument
`ti`, above a frame of `F` bytes), among `ts`, in a frame pushing `rs` (its
arguments): the table's address into `ebx`, its word `j` into `ebx`, then
`call ebx`. -/
def tcall (F ti j : Nat) (ts : List (String × Prog isa)) (rs : List Reg) : Prog isa :=
  .seq (.block [.mov .ebx (argM F ti)]) (.seq (.block [.mov .ebx (.mem (at_ .ebx (4 * j)))])
    (.frame (.push rs) (Code.icalls (.callr .ebx) ts) (.pop .eax rs.length)))

/-- The `ecx` bytes at `esi` to `ebx` (`ecx > 0`), a byte at a time, `ebx`
and `esi` past them. -/
def cpLoop : Prog isa := Impl.Bignum.X86.copyBytes

/-! ## Keying HMAC -/

/-- `key`'s frame: our caller's registers, then the working space of `init`
for a key of any length (the most: SHA-512's `W + S` words). -/
def kWork : Nat := 16
def kFr : Nat := 3424

/-- `init`'s arguments: the states at `key` and `key + 192` (`edi`, `esi`),
`PRK` as the key (`edx`, `ecx`), the working space (`ebp`). -/
def keyArgs : List Instr :=
  [.mov .edi (argM kFr 2), .mov .esi (.reg .edi), .alu .add .esi (.imm 192), .mov .edx (argM kFr 0),
    .mov .ecx (argM kFr 1)] ++ fr .ebp kWork

/-- The frame's body of `vg_hkdf_key`, whose table's `init` may be `f`'s. -/
def keyBody (f : Fns) : Prog isa :=
  .seq (.block (entry kFr 3)) (.seq (.block keyArgs) (.seq (tcall kFr 3 0 f.init init5) (.block restoreRegs)))

/-- `vg_hkdf_key`. -/
def key (f : Fns) : Prog isa := .frame (.alloc kFr) (keyBody f) (.free kFr)

/-! ## HKDF-Extract -/

/-! Where things are in `extract`'s frame: our caller's registers, `B`,
HMAC's inner and outer states (192 bytes each), then the working space. -/
def xB : Nat := 16
def xIn : Nat := 20
def xOut : Nat := 212
def xWork : Nat := 404
/-- `extract`'s frame's size. -/
def xFr : Nat := 3812

/-- `B`, the table's word of data 5 (the table in `eax`), to the frame. -/
def extractTab : List Instr := [.mov .ecx (.mem (at_ .eax 20)), .store (sp xB) .ecx]

/-- `init`'s arguments: the states (`edi`, `esi`), the salt as the key
(`edx`, `ecx`), the working space (`ebp`). -/
def extractInit : List Instr :=
  fr .edi xIn ++ fr .esi xOut ++ [.mov .edx (argM xFr 0), .mov .ecx (argM xFr 1)] ++ fr .ebp xWork

/-- `update`'s arguments: the inner state (`edi`), the `B` bytes it holds
(`esi`, and `eax` the high word), the input keying material (`edx`,
`ecx`), the working space (`ebp`). -/
def extractUpd : List Instr :=
  fr .edi xIn ++ [.mov .esi (.mem (sp xB)), .mov .eax (.imm 0), .mov .edx (argM xFr 2), .mov .ecx (argM xFr 3)] ++
    fr .ebp xWork

/-- `finalize`'s arguments: the states (`edx`, `esi`), the `B + ikm_len`
bytes the inner one holds (`eax`, and `ecx` the high word), `prk` (`edi`),
the working space (`ebp`). -/
def extractFin : List Instr :=
  fr .edx xIn ++ fr .esi xOut ++
    [.mov .eax (.mem (sp xB)), .alu .add .eax (argM xFr 3), .mov .ecx (.imm 0), .mov .edi (argM xFr 4)] ++
    fr .ebp xWork

/-- The frame's body of `vg_hkdf_extract`, whose table's functions may be
`f`'s. -/
def extractBody (f : Fns) : Prog isa :=
  .seq (.block (entry xFr 6)) (.seq (.block extractTab)
  (.seq (.block extractInit) (.seq (tcall xFr 6 0 f.init init5)
  (.seq (.block extractUpd) (.seq (tcall xFr 6 1 f.upd upd6)
  (.seq (.block extractFin) (.seq (tcall xFr 6 2 f.fin fin6) (.block restoreRegs))))))))

/-- `vg_hkdf_extract`. -/
def extract (f : Fns) : Prog isa := .frame (.alloc xFr) (extractBody f) (.free xFr)

/-! ## HKDF-Expand -/

/-! Where things are in `expand`'s frame: our caller's registers, `D` and
`B`, the counter `i`, the bytes of `out` left, the next byte of `out` to
write, the length of `T(i - 1)`, the working state (192 bytes), `T(i)` (64
bytes), the counter's byte (in a word), then the working space of `update`
and `finalize`. -/
def eD : Nat := 16
def eB : Nat := 20
def eCnt : Nat := 24
def eRem : Nat := 28
def eOut : Nat := 32
def eTl : Nat := 36
def eW : Nat := 40
def eT : Nat := 232
def eC : Nat := 296
def eWork : Nat := 300
/-- `expand`'s frame's size: the working space of `update` and `finalize`
is at most 1872 bytes. -/
def eFr : Nat := 2172

/-- `D` and `B` (the table in `eax`) to the frame; `i = 1`, `rem = out_len`,
`out`, `T(0)` empty; and whether `out_len` is 0. -/
def expandTab : List Instr :=
  [.mov .ecx (.mem (at_ .eax 16)), .store (sp eD) .ecx, .mov .ecx (.mem (at_ .eax 20)), .store (sp eB) .ecx,
    .mov .ecx (.imm 1), .store (sp eCnt) .ecx, .mov .ecx (argM eFr 3), .store (sp eOut) .ecx,
    .mov .ecx (.imm 0), .store (sp eTl) .ecx, .mov .ecx (argM eFr 4), .store (sp eRem) .ecx,
    .alu .test .ecx (.reg .ecx)]

/-- The copy's arguments: the inner state at `key` (`esi`), the working
state (`ebx`), its 192 bytes (`ecx`). -/
def copyA : List Instr := [.mov .esi (argM eFr 0), .mov .ebx (.reg .esp), .alu .add .ebx (.imm (BitVec.ofNat 32 eW)),
  .mov .ecx (.imm 192)]

/-- `update`'s arguments for `T(i - 1)`: the working state, which holds `B`
bytes, the `tlen` bytes at `T`, the working space. -/
def updT : List Instr :=
  fr .edi eW ++ [.mov .esi (.mem (sp eB)), .mov .eax (.imm 0)] ++ fr .edx eT ++ [.mov .ecx (.mem (sp eTl))] ++
    fr .ebp eWork

/-- `update`'s arguments for `info`: the working state, which holds
`B + tlen` bytes. -/
def updI : List Instr :=
  fr .edi eW ++ [.mov .esi (.mem (sp eB)), .alu .add .esi (.mem (sp eTl)), .mov .eax (.imm 0),
    .mov .edx (argM eFr 1), .mov .ecx (argM eFr 2)] ++ fr .ebp eWork

/-- The counter's byte stored; `update`'s arguments for it: the working
state, which holds `B + tlen + info_len` bytes, and the byte. -/
def updC : List Instr :=
  [.mov .eax (.mem (sp eCnt)), .store8 (sp eC) .al] ++ fr .edi eW ++
    [.mov .esi (.mem (sp eB)), .alu .add .esi (.mem (sp eTl)), .alu .add .esi (argM eFr 2), .mov .eax (.imm 0)] ++
    fr .edx eC ++ [.mov .ecx (.imm 1)] ++ fr .ebp eWork

/-- `finalize`'s arguments: the working state (`edx`), which holds
`B + tlen + info_len + 1` bytes (`eax`, and `ecx` the high word), the outer
state at `key + 192` (`esi`), `T` (`edi`), the working space (`ebp`). -/
def finT : List Instr :=
  fr .edx eW ++ [.mov .esi (argM eFr 0), .alu .add .esi (.imm 192), .mov .eax (.mem (sp eB)),
    .alu .add .eax (.mem (sp eTl)), .alu .add .eax (argM eFr 2), .alu .add .eax (.imm 1), .mov .ecx (.imm 0)] ++
    fr .edi eT ++ fr .ebp eWork

/-- `D` and `rem`, compared. -/
def outCmp : List Instr := [.mov .ecx (.mem (sp eD)), .mov .edx (.mem (sp eRem)), .alu .cmp .edx (.reg .ecx)]

/-- The bytes of `T(i)` to copy, `n = min(D, rem)`, into `ecx`: `D`, or
`rem` if it is less (both public). -/
def outLen : Prog isa :=
  .seq (.block outCmp) (.ite .b (.block [.mov .ecx (.reg .edx)]) (.block []))

/-- The copy's arguments: `n` kept in `edi`, `out`'s next byte (`ebx`),
`T` (`esi`). -/
def outA : List Instr := [.mov .edi (.reg .ecx), .mov .ebx (.mem (sp eOut))] ++ fr .esi eT

/-- After the copy: `out` past the bytes written (`ebx`), `rem` less them,
`T(i)`'s `D` bytes the next block's `T(i - 1)`, the next counter; whether
bytes of `out` are left. -/
def nextBlock : List Instr :=
  [.store (sp eOut) .ebx, .mov .edx (.mem (sp eRem)), .alu .sub .edx (.reg .edi), .store (sp eRem) .edx,
    .mov .ecx (.mem (sp eD)), .store (sp eTl) .ecx, .mov .eax (.mem (sp eCnt)), .alu .add .eax (.imm 1),
    .store (sp eCnt) .eax, .alu .test .edx (.reg .edx)]

/-- One block `T(i)`, whose table's functions may be `f`'s. -/
def block (f : Fns) : Prog isa :=
  .seq (.block copyA) (.seq cpLoop
  (.seq (.block updT) (.seq (tcall eFr 5 1 f.upd upd6)
  (.seq (.block updI) (.seq (tcall eFr 5 1 f.upd upd6)
  (.seq (.block updC) (.seq (tcall eFr 5 1 f.upd upd6)
  (.seq (.block finT) (.seq (tcall eFr 5 2 f.fin fin6)
  (.seq outLen (.seq (.block outA) (.seq cpLoop (.block nextBlock)))))))))))))

/-- The frame's body of `vg_hkdf_expand`, whose table's functions may be
`f`'s: the blocks while bytes of `out` are left. -/
def expandBody (f : Fns) : Prog isa :=
  .seq (.block (entry eFr 5)) (.seq (.block expandTab)
    (.seq (.ite .ne (.loop (block f) .ne) (.block [])) (.block restoreRegs)))

/-- `vg_hkdf_expand`. -/
def expand (f : Fns) : Prog isa := .frame (.alloc eFr) (expandBody f) (.free eFr)

end VG.Impl.Hkdf.X86
