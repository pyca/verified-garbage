module

public import VerifiedGarbage.Impl.Sm4.X86.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4's round keys prepared once, and batches under them, on x86 (32-bit)

`vg_sm4_prepare_keys` and `vg_sm4_crypt_prepared`
(`Proof/Sm4/Prepared.lean`): the table of round keys and the bitsliced core
(`Ecb.lean`) as functions of the working space, for the modes, which call
them (`Modes.lean`), and for ECB (`ecb`, below), which calls the second.
Both are cdecl, their arguments at `[esp + 4]` on.

* `prepareKeys(schedule, decrypt, ws, ws_len)` saves the callee-saved
  registers in their slots (352–355) of `ws`, which moves to `edi`, builds
  the table of bitsliced round keys in the order `decrypt` selects (public)
  and restores the registers.
* `cryptPrepared(ws, ws_len)` saves the registers the same way and
  transforms the eight blocks of the tail buffer (`crypt8`) under the table.

Their working space is 358 slots (`slots`). The table is what
`vg_sm4_crypt_prepared` reads of the preparation (`layout`): each plane of a
round key is a 32-bit word whose bit `8 i + b` is bit `j` of the key's byte
`i` (`planeOf32`), for every block `b`.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86

open VG.X86 VG.Impl.Aes.X86

/-- `vg_sm4_prepare_keys`: the table of the direction the second argument
selects. -/
def prepareKeys : Prog isa :=
  .seq (.block (saveRegs 2 ++ [.mov .eax (.mem (argOp 1)), .alu .test .eax (.reg .eax)]))
    (.seq (.ite .e (keys .encrypt) (keys .decrypt)) (.block restoreRegs))

/-- `vg_sm4_crypt_prepared`: the eight blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block (saveRegs 0)) (.seq crypt8 (.block restoreRegs))

/-! ## The layout -/

/-- The direction of the specification. -/
def ofSpecDir : Spec.Sm4.Direction → Dir
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- The round key of the table's entry `e`, for the round keys `k` in the
order of the direction. -/
def keyEntry (k : Spec.Sm4.Schedule) : Dir → Nat → Spec.Sm4.Word
  | .encrypt, e => k.getD e 0
  | .decrypt, e => k.getD (31 - e) 0

/-- The word of slot `w` of the table: plane `w % 8` of its entry. -/
def preparedWord (k : Spec.Sm4.Schedule) (d : Dir) (w : Nat) : BitVec 32 :=
  Impl.Sm4.planeOf32 (keyEntry k d ((w - tableSlot) / 8)) ((w - tableSlot) % 8)

/-! ## The calls -/

/-- The working space's length in 64-bit words, `ws_len`. -/
def wsWords : Nat := 4 * slots / 8

/-- The value of `decrypt` for a direction. -/
def dirFlagOf : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

/-- A call of `vg_sm4_prepare_keys` for the direction `d`, with the schedule
the mode's first argument and the working space at `edi`, of `slots` slots
(`wsWords` 64-bit words): the arguments pushed, the last first. `edi`, which
the function restores, is loaded again from the modes' fifth argument, the
working space: the analysis of constant time forgets which slot holds it
across the function's stores through a pointer into the table. -/
def prepareCall (d : Dir) : Prog isa :=
  .seq (.block [movI .eax (BitVec.ofNat 32 wsWords), movI .edx (BitVec.ofNat 32 (dirFlagOf d)),
      .mov .ecx (.mem (argOp 0))])
    (.seq (.frame (.push [.eax, .edi, .edx, .ecx])
      (.call "vg_sm4_prepare_keys" prepareKeys) (.pop .eax 4))
      (.block [.mov .edi (.mem (argOp 4))]))

/-- A call of `vg_sm4_crypt_prepared` on the working space at `edi`. The
modes' data pointer and steps left wait in `esi` and `ebp`, which the
function restores, and go back to their slots after it: the analysis of
constant time forgets what the scratch buffer holds across the function's
stores. -/
def cryptCall : Prog isa :=
  .seq (.block [movS .esi modeDSlot, movS .ebp modeNSlot, movI .eax (BitVec.ofNat 32 wsWords)])
    (.seq (.frame (.push [.eax, .edi]) (.call "vg_sm4_crypt_prepared" cryptPrepared) (.pop .eax 2))
      (.block [st modeDSlot .esi, st modeNSlot .ebp]))

/-! ## ECB

`ecb dir(schedule, data, n, scratch)`, cdecl (the arguments at `[esp + 4]`
… `[esp + 16]`): `vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt`, with their
working space in the scratch buffer, which the artifact allocates on the
stack: the functions' 358 slots, then ECB's own where the modes keep theirs
(`Impl/Modes/X86/Seq.lean`), 368 slots in all (`[u64; 184]`), and 20 bytes
of stack for the calls.

* The callee-saved registers are saved in the slots after the functions'
  (`ecbSaved`), which `vg_sm4_crypt_prepared` does not change, and the
  scratch buffer's address moves to `edi`.
* The round keys are bitsliced into the table in the order of `dir`
  (`keys`), and the data pointer and `n` go to their slots.
* Each group of up to eight blocks is copied to the tail buffer, transformed
  there by `vg_sm4_crypt_prepared` (`cryptCall`), which costs the same for
  any number of the buffer's blocks, and copied back.
-/

/-- ECB's callee-saved registers, and their slots after the functions'. -/
def ecbSaved : List (Reg × Nat) := [(.ebx, slots), (.esi, slots + 1), (.edi, slots + 2), (.ebp, slots + 3)]

/-- The scratch buffer (the fourth argument) to `edi`, the callee-saved
registers to their slots first. -/
def ecbEntry : List Instr :=
  [.mov .eax (.mem (argOp 3))] ++ ecbSaved.map (fun (r, j) => .store (slotAt .eax j) r) ++ [movR .edi .eax]

/-- Restore the registers (`edi`, the base, last). -/
def ecbRestore : List Instr :=
  [movS .ebx slots, movS .esi (slots + 1), movS .ebp (slots + 3), movS .edi (slots + 2)]

/-- Eight blocks, or the last one to seven. -/
def group : Prog isa := .seq copyIn (.seq cryptCall (.seq copyOut advance))

/-- The whole function: the table, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block ecbEntry)
    (.seq (keys dir)
      (.seq (.block [.mov .eax (.mem (argOp 1)), st modeDSlot .eax, .mov .eax (.mem (argOp 2)), st modeNSlot .eax,
          .alu .test .eax (.reg .eax)])
        (.seq (.ite .e (.block []) (.loop group .ne)) (.block ecbRestore))))

end VG.Impl.Sm4.X86
