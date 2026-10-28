module

public import VerifiedGarbage.Impl.CmacAes.RISCV64
public import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.Loops

/-!
# Streaming AES-CMAC: RISC-V implementation

`vg_cmac_aes_init(state = a0, key = a1, key_len = a2, scratch = a3)`,
`vg_cmac_aes_absorb(state = a0, rounds = a1, count = a2, data = a3, len = a4, scratch = a5)`
and `vg_cmac_aes_finish(state = a0, rounds = a1, count = a2, out = a3, scratch = a4)`
(see `VG.Spec.Cmac.aesInitContract` and the others), composed of calls of
the verified `vg_aes_expand_key_scratch`, `vg_cmac_aes_subkeys`,
`vg_cmac_aes_update` and `vg_cmac_aes_finalize`, as on PPC64LE
(`VG.Impl.CmacAes.Stream.PPC64LE`).

The state (`VG.Spec.Cmac.Repr`) is the key schedule (bytes 0–239), the
subkeys (240–271), the chaining value (272–287) and the bytes held back
(288–303), so bytes 0–271 are `vg_cmac_aes_finalize`'s `key`. The scratch
buffer (2304 bytes): `[0, 2176)` is the working space of the functions
called, and from `scratch + 2176` rounded up to a multiple of 8 (`savePtr2`),
our return address (which each call replaces) and the callee-saved
registers we use. The contracts state no alignment for the state, the key,
the data and `out`, so they are accessed a byte at a time.

* `init` expands the key into the state, derives the subkeys after it and
  zeroes the chaining value, keeping the state (`s1`), the scratch buffer
  (`s2`) and the rounds (`s3`) across the calls.
* `absorb` keeps the state (`s1`), the rounds (`s2`), the data left (`s3`,
  `s4` bytes), the bytes of whole blocks chained by the second call (`s5`)
  and the scratch buffer (`s6`) across the calls, as on PPC64LE: with `h`
  bytes held back, it copies `f = min(len, 16 - h)` bytes after them; if data
  is left, it chains that block, then the whole blocks of what is left but
  its last 1 to 16 bytes, which it copies to the start of the bytes held
  back. With no data left, the two calls chain no blocks and the second copy
  copies nothing, so the code has no branch around a call.
* `finish` copies the chaining value to `out` and calls
  `vg_cmac_aes_finalize` with the state as its key, `out` as its state and
  the `h` bytes held back as the last bytes, keeping only the scratch buffer
  (in `s1`) across the call.

The branches are on whether a register is zero and on `sltu`'s results.
Only the pointers, the key length, `count` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.CmacAes.Stream.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov)

/-- A call of `vg_aes_expand_key_scratch`. -/
def ekCall : Prog isa := .call "vg_aes_expand_key_scratch" Impl.Aes.RISCV64.expandKey

/-- A call of `vg_cmac_aes_subkeys`. -/
def skCall : Prog isa := .call "vg_cmac_aes_subkeys" Impl.CmacAes.RISCV64.subkeys

/-- A call of `vg_cmac_aes_update`. -/
def updCall : Prog isa := .call "vg_cmac_aes_update" Impl.CmacAes.RISCV64.update

/-- A call of `vg_cmac_aes_finalize`. -/
def finCall : Prog isa := .call "vg_cmac_aes_finalize" Impl.CmacAes.RISCV64.finalize

/-- `t0 :=` `n + 2176` rounded up to a multiple of 8 (`(n + 2183) & -8`), where
the registers are saved. -/
def savePtr2 (n : Reg) : List Instr := [.addi .t0 n 2047, .addi .t0 .t0 136, .logicImm .and .t0 .t0 (-8)]

/-! ## `vg_cmac_aes_init` -/

/-- The registers `init` saves, and their offsets from `t0`. -/
def initSaved : List (Reg × Nat) := [(.ra, 0), (.s1, 8), (.s2, 16), (.s3, 24)]

/-- Saves them (with the scratch buffer in `a3`), keeps the state in `s1`, the
scratch buffer in `s2` and the rounds (`key_len / 4 + 6`) in `s3`, and sets up
the arguments of
`vg_aes_expand_key_scratch(key = a0, key_len = a1, schedule = a2, scratch = a3)`. -/
def initPre : List Instr :=
  savePtr2 .a3 ++ initSaved.map (fun (r, d) => .store .d r .t0 d) ++
    [mov .s1 .a0, mov .s2 .a3, .shift .srl .d .s3 .a2 2, .addi .s3 .s3 6, mov .a0 .a1, mov .a1 .a2,
     mov .a2 .s1]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = a0, rounds = a1, subkeys = a2, scratch = a3)`. -/
def initMid : List Instr := [mov .a0 .s1, mov .a1 .s3, .addi .a2 .s1 240, mov .a3 .s2]

/-- The chaining value zeroed, a byte at a time, and the registers restored
(with the scratch buffer in `s2`). -/
def initPost : List Instr :=
  storeBytes .t1 .s1 272 (List.replicate 16 0) ++ savePtr2 .s2 ++
    initSaved.map (fun (r, d) => .load .d r .t0 d)

def init : Prog isa :=
  .seq (.block initPre) (.seq ekCall (.seq (.block initMid) (.seq skCall (.block initPost))))

/-! ## Copying bytes -/

/-- The `t2` bytes at `t6` (none if `t2` is 0) copied to `t5`, a byte at a time. -/
def copy : Prog isa := .ite (.zero .t2) (.block []) (copyLoop .t3 .t6 .t5 .t2)

/-! ## `vg_cmac_aes_absorb` -/

/-- The registers `absorb` saves, and their offsets from `t0`. -/
def absSaved : List (Reg × Nat) :=
  [(.ra, 0), (.s1, 8), (.s2, 16), (.s3, 24), (.s4, 32), (.s5, 40), (.s6, 48)]

/-- Saves them (with the scratch buffer in `a5`) and keeps the arguments in
them. -/
def save : List Instr :=
  savePtr2 .a5 ++ absSaved.map (fun (r, d) => .store .d r .t0 d) ++
    [mov .s1 .a0, mov .s2 .a1, mov .s3 .a3, mov .s4 .a4, mov .s6 .a5]

/-- The number of bytes held back for `count` (`a2`), in `t1`. -/
def held : Prog isa :=
  .ite (.zero .a2) (.block [.li .t1 0])
    (.block [.addi .t1 .a2 (-1), .logicImm .and .t1 .t1 15, .addi .t1 .t1 1])

/-- `min(len, 16)` in `t2`. -/
def clamp : Prog isa :=
  .seq (.block [.shift .srl .d .t2 .s4 4]) (.ite (.zero .t2) (.block [mov .t2 .s4]) (.block [.li .t2 16]))

/-- `f = min(len, 16 - h)` in `t2` (the count of the copy) and `a7`, the
destination `state + 288 + h` in `t5` and the source in `t6`. -/
def fill : Prog isa :=
  .seq clamp
    (.seq (.block [.li .t3 16, .sub .t3 .t3 .t1, .sltu .t4 .t2 .t3])
      (.seq (.ite (.zero .t4) (.block [mov .t2 .t3]) (.block []))
        (.block [mov .a7 .t2, .add .t5 .s1 .t1, .addi .t5 .t5 288, mov .t6 .s3])))

/-- The data advanced past the `f` bytes copied; one block to chain (`a4`)
if data is left, else none; and the other arguments of
`vg_cmac_aes_update(schedule = a0, rounds = a1, state = a2, data = a3, n = a4, scratch = a5)`
for the block held back. -/
def chain1 : Prog isa :=
  .seq (.block [.add .s3 .s3 .a7, .sub .s4 .s4 .a7, .li .a4 0])
    (.seq (.ite (.zero .s4) (.block []) (.block [.li .a4 1]))
      (.block [mov .a0 .s1, mov .a1 .s2, .addi .a2 .s1 272, .addi .a3 .s1 288, mov .a5 .s6]))

/-- `16 nb` in `s5` for the `nb` whole blocks of the data left but its last
1 to 16 bytes (none if no data is left), and the arguments of
`vg_cmac_aes_update` for them. -/
def chain2 : Prog isa :=
  .seq (.block [.li .s5 0])
    (.seq (.ite (.zero .s4) (.block [])
        (.block [.addi .s5 .s4 (-1), .logicImm .and .t1 .s5 15, .sub .s5 .s5 .t1]))
      (.block [.shift .srl .d .a4 .s5 4, mov .a0 .s1, mov .a1 .s2, .addi .a2 .s1 272, mov .a3 .s3,
        mov .a5 .s6]))

/-- The data advanced past the blocks chained, and the arguments of the
copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.add .s3 .s3 .s5, .sub .s4 .s4 .s5, .addi .t5 .s1 288, mov .t6 .s3, mov .t2 .s4]

/-- Restores the registers, with the scratch buffer in `s6`. -/
def restore : List Instr := savePtr2 .s6 ++ absSaved.map (fun (r, d) => .load .d r .t0 d)

/-- Everything before the first call. -/
def absorbPre : Prog isa := .seq (.block save) (.seq held (.seq fill (.seq copy chain1)))

/-- Everything after the second call. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block restore))

def absorb : Prog isa := .seq absorbPre (.seq updCall (.seq chain2 (.seq updCall absorbPost)))

/-! ## `vg_cmac_aes_finish` -/

/-- The registers `finish` saves, and their offsets from `t0`. -/
def finSaved : List (Reg × Nat) := [(.ra, 0), (.s1, 8)]

/-- The chaining value copied to `out`, a byte at a time, the registers saved
(with the scratch buffer in `a4`) and the scratch buffer kept in `s1`, and
the arguments of
`vg_cmac_aes_finalize(key = a0, rounds = a1, state = a2, last = a3, last_len = a4, scratch = a5)`
but `last_len`, which is `count` in `a4` so far. -/
def finishPre : List Instr :=
  copyBytes .t1 .a0 .a3 272 0 16 ++ savePtr2 .a4 ++ finSaved.map (fun (r, d) => .store .d r .t0 d) ++
    [mov .s1 .a4, mov .a5 .a4, mov .a4 .a2, mov .a2 .a3, .addi .a3 .a0 288]

/-- `last_len`: the number of bytes held back for `count` (in `a4`). -/
def lastLen : Prog isa :=
  .ite (.zero .a4) (.block []) (.block [.addi .a4 .a4 (-1), .logicImm .and .a4 .a4 15, .addi .a4 .a4 1])

/-- Everything before the call. -/
def finPre : Prog isa := .seq (.block finishPre) lastLen

/-- The registers restored, with the scratch buffer in `s1`. -/
def finishPost : List Instr := savePtr2 .s1 ++ finSaved.map (fun (r, d) => .load .d r .t0 d)

def finish : Prog isa := .seq finPre (.seq finCall (.block finishPost))

end VG.Impl.CmacAes.Stream.RISCV64
