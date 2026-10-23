module

public import VerifiedGarbage.Impl.CmacAes.PPC64LE
public import VerifiedGarbage.Impl.Aes.PPC64LE.ExpandKey

/-!
# Streaming AES-CMAC: PPC64LE implementation

`vg_cmac_aes_init(state = r3, key = r4, key_len = r5, scratch = r6)`,
`vg_cmac_aes_absorb(state = r3, rounds = r4, count = r5, data = r6, len = r7, scratch = r8)`
and `vg_cmac_aes_finish(state = r3, rounds = r4, count = r5, out = r6, scratch = r7)`
(see `VG.Spec.Cmac.aesInitContract` and the others), composed of calls of
the verified `vg_aes_expand_key_scratch`, `vg_cmac_aes_subkeys`,
`vg_cmac_aes_update` and `vg_cmac_aes_finalize`, as on AArch64
(`VG.Impl.CmacAes.Stream.AArch64`).

The state (`VG.Spec.Cmac.Repr`) is the key schedule (bytes 0–239), the
subkeys (240–271), the chaining value (272–287) and the bytes held back
(288–303), so bytes 0–271 are `vg_cmac_aes_finalize`'s `key`. The scratch
buffer (2304 bytes): `[0, 2176)` is the working space of the functions
called, and `[2176, 2232)` our caller's nonvolatile registers and our
return address (a call replaces the link register). A call (`bl`) stores
nothing in memory, so no stack is used.

* `init` expands the key into the state, derives the subkeys after it and
  zeroes the chaining value, keeping the state (`r14`), the scratch buffer
  (`r15`) and the rounds (`r16`) across the calls.
* `absorb` keeps the state (`r14`), the rounds (`r15`), the data left
  (`r16`, `r17` bytes), the bytes of whole blocks chained by the second
  call (`r18`) and the scratch buffer (`r19`) across the calls. With `h`
  bytes held back (`count` modulo 16, but 16 for a multiple of 16 and 0 for
  the empty message), it copies `f = min(len, 16 - h)` bytes after them. If
  data is left (the block held back is whole and not the last), it chains
  that block, then the whole blocks of what is left but its last 1 to 16
  bytes, which it copies to the start of the bytes held back. With no data
  left, the two calls chain no blocks and the second copy copies nothing,
  so the code has no branch around a call.
* `finish` copies the chaining value to `out` and calls
  `vg_cmac_aes_finalize` with the state as its key, `out` as its state and
  the `h` bytes held back as the last bytes, keeping only the scratch buffer
  (in `r14`) across the call.

The model has no flags: the branches are on whether a register is zero,
and `min(len, 16 - h)` is `min(min(len, 16), 16 - h)`, the first by whether
`len >> 4` is 0, the second by the sign of a difference of two numbers of at
most 16. Only the pointers, the key length, `count` and `len` can affect
timing: the branches are on them, and so are the number of bytes copied and
of blocks chained.
-/

@[expose] public section

namespace VG.Impl.CmacAes.Stream.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov)

/-- A call of `vg_aes_expand_key_scratch`. -/
def ekCall : Prog isa := .call "vg_aes_expand_key_scratch" Impl.Aes.PPC64LE.expandKey

/-- A call of `vg_cmac_aes_subkeys`. -/
def skCall : Prog isa := .call "vg_cmac_aes_subkeys" Impl.CmacAes.PPC64LE.subkeys

/-- A call of `vg_cmac_aes_update`. -/
def updCall : Prog isa := .call "vg_cmac_aes_update" Impl.CmacAes.PPC64LE.update

/-- A call of `vg_cmac_aes_finalize`. -/
def finCall : Prog isa := .call "vg_cmac_aes_finalize" Impl.CmacAes.PPC64LE.finalize

/-! ## `vg_cmac_aes_init` -/

/-- The registers saved in the scratch buffer, and where (`r15`, the base of
the restore, last). -/
def initSaved : List (Reg × Nat) := [(.r0, 2200), (.r14, 2176), (.r16, 2192), (.r15, 2184)]

/-- Saves the registers and the return address, keeps the state in `r14`,
the scratch buffer in `r15` and the rounds (`key_len / 4 + 6`) in `r16`, and
sets up the arguments of
`vg_aes_expand_key_scratch(key = r3, key_len = r4, schedule = r5, scratch = r6)`. -/
def initPre : List Instr :=
  .mflr .r0 :: initSaved.map (fun (r, d) => .store .d r .r6 d) ++
  [mov .r14 .r3, mov .r15 .r6, .lsr .d .r16 .r5 2, .addi .r16 .r16 6, mov .r3 .r4, mov .r4 .r5,
   mov .r5 .r14]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = r3, rounds = r4, subkeys = r5, scratch = r6)`. -/
def initMid : List Instr := [mov .r3 .r14, mov .r4 .r16, .addi .r5 .r14 240, mov .r6 .r15]

/-- The chaining value zeroed, and the registers and the return address
restored. -/
def initPost : List Instr :=
  [.li .r9 0, .store .d .r9 .r14 272, .store .d .r9 .r14 280] ++
    initSaved.map (fun (r, d) => .load .d r .r15 d) ++ [.mtlr .r0]

def init : Prog isa := .seq (.block initPre) (.seq ekCall (.seq (.block initMid) (.seq skCall (.block initPost))))

/-! ## Copying bytes -/

/-- The `r12` bytes at `r11` (none if `r12` is 0) copied to `r10`, a byte at a time. -/
def copy : Prog isa := .ite (.zero .d .r12) (.block []) Impl.CmacAes.PPC64LE.copy

/-! ## `vg_cmac_aes_absorb` -/

/-- The registers saved in the scratch buffer, and where (`r19`, the base of
the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.r0, 2176), (.r14, 2184), (.r15, 2192), (.r16, 2200), (.r17, 2208), (.r18, 2216), (.r19, 2224)]

/-- Saves the registers and the return address and keeps the arguments in them. -/
def save : List Instr :=
  .mflr .r0 :: saved.map (fun (r, d) => .store .d r .r8 d) ++
  [mov .r14 .r3, mov .r15 .r4, mov .r16 .r6, mov .r17 .r7, mov .r19 .r8]

/-- The number of bytes held back for `count` (`r5`), in `r9`. -/
def held : Prog isa :=
  .ite (.zero .d .r5) (.block [.li .r9 0])
    (.block [.subi .r9 .r5 1, .li .r10 15, .logic .and .r9 .r9 .r10, .addi .r9 .r9 1])

/-- `min(len, 16)` in `r10`. -/
def clamp : Prog isa :=
  .seq (.block [.lsr .d .r10 .r17 4])
    (.ite (.zero .d .r10) (.block [mov .r10 .r17]) (.block [.li .r10 16]))

/-- `f = min(len, 16 - h)` in `r12` (the count of the copy) and `r8`, the
destination `state + 288 + h` in `r10` and the source in `r11`. -/
def fill : Prog isa :=
  .seq clamp
    (.seq (.block [.li .r12 16, .sub .r12 .r12 .r9, .sub .r11 .r10 .r12, .lsr .d .r11 .r11 63])
      (.seq (.ite (.zero .d .r11) (.block []) (.block [mov .r12 .r10]))
        (.block [mov .r8 .r12, .add .r10 .r14 .r9, .addi .r10 .r10 288, mov .r11 .r16])))

/-- The data advanced past the `f` bytes copied; one block to chain (`r7`)
if data is left, else none; and the other arguments of
`vg_cmac_aes_update(schedule = r3, rounds = r4, state = r5, data = r6, n = r7, scratch = r8)`
for the block held back. -/
def chain1 : Prog isa :=
  .seq (.block [.add .r16 .r16 .r8, .sub .r17 .r17 .r8, .li .r7 0])
    (.seq (.ite (.zero .d .r17) (.block []) (.block [.li .r7 1]))
      (.block [mov .r3 .r14, mov .r4 .r15, .addi .r5 .r14 272, .addi .r6 .r14 288, mov .r8 .r19]))

/-- `16 nb` in `r18` for the `nb` whole blocks of the data left but its last
1 to 16 bytes (none if no data is left), and the arguments of
`vg_cmac_aes_update` for them. -/
def chain2 : Prog isa :=
  .seq (.block [.li .r18 0])
    (.seq (.ite (.zero .d .r17) (.block [])
        (.block [.subi .r18 .r17 1, .li .r9 15, .logic .and .r9 .r18 .r9, .sub .r18 .r18 .r9]))
      (.block [.lsr .d .r7 .r18 4, mov .r3 .r14, mov .r4 .r15, .addi .r5 .r14 272, mov .r6 .r16,
        mov .r8 .r19]))

/-- The data advanced past the blocks chained, and the arguments of the
copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.add .r16 .r16 .r18, .sub .r17 .r17 .r18, .addi .r10 .r14 288, mov .r11 .r16, mov .r12 .r17]

/-- Restores the registers and the return address, with `r19` (restored
last) the scratch buffer. -/
def restore : List Instr := saved.map (fun (r, d) => .load .d r .r19 d) ++ [.mtlr .r0]

/-- Everything before the first call. -/
def absorbPre : Prog isa := .seq (.block save) (.seq held (.seq fill (.seq copy chain1)))

/-- Everything after the second call. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block restore))

def absorb : Prog isa := .seq absorbPre (.seq updCall (.seq chain2 (.seq updCall absorbPost)))

/-! ## `vg_cmac_aes_finish` -/

/-- The registers `finish` saves in the scratch buffer, and where (`r14`,
the base of the restore, last). -/
def finSaved : List (Reg × Nat) := [(.r0, 2184), (.r14, 2176)]

/-- The chaining value copied to `out`, `r14` and the return address saved
and the scratch buffer kept in `r14`, and the arguments of
`vg_cmac_aes_finalize(key = r3, rounds = r4, state = r5, last = r6, last_len = r7, scratch = r8)`
but `last_len`, which is `count` in `r7` so far. -/
def finishPre : List Instr :=
  [.mflr .r0, .load .d .r9 .r3 272, .store .d .r9 .r6 0, .load .d .r9 .r3 280, .store .d .r9 .r6 8] ++
    finSaved.map (fun (r, d) => .store .d r .r7 d) ++
    [mov .r14 .r7, mov .r8 .r7, mov .r7 .r5, mov .r5 .r6, .addi .r6 .r3 288]

/-- `last_len`: the number of bytes held back for `count` (in `r7`). -/
def lastLen : Prog isa :=
  .ite (.zero .d .r7) (.block [])
    (.block [.subi .r7 .r7 1, .li .r9 15, .logic .and .r7 .r7 .r9, .addi .r7 .r7 1])

/-- Everything before the call. -/
def finPre : Prog isa := .seq (.block finishPre) lastLen

/-- The registers and the return address restored. -/
def finishPost : List Instr := finSaved.map (fun (r, d) => .load .d r .r14 d) ++ [.mtlr .r0]

def finish : Prog isa := .seq finPre (.seq finCall (.block finishPost))

end VG.Impl.CmacAes.Stream.PPC64LE
