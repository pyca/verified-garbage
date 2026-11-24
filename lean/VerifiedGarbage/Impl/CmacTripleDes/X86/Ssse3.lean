module

public import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# Streaming TDEA-CMAC on x86 (32-bit) with Triple DES's S-boxes by `pshufb`

`vg_cmac_triple_des_absorb_ssse3` and `vg_cmac_triple_des_finish_ssse3`:
the streaming functions' code around the runs (`absorbWith`, `finishWith`
of `Impl/CmacTripleDes/Stream/X86.lean`) over runs that chain blocks with
the block function of Triple DES's one-block core
(`Impl.TripleDes.X86.Ssse3.crypt`). `vg_cmac_triple_des_stream_init` has no
such variant.

`chain`, the internal function `vg_cmac_triple_des_chain_ssse3`, is a run of
`update` on registers: the key schedule in `eax`, the chaining value's
address in `edx`, the blocks' in `ebx`, their number in `esi` and the
working space in `edi`, of which it uses the first 464 bytes; it keeps
`ebx`, `esi`, `edi`, `ebp` and `esp`. With no blocks it does nothing.
Otherwise the working space is the block function's buffer in its first 432
bytes (the table's address, the block at byte 8, the two slots of the
halves, the rounds' keys from byte 48); the function keeps the three
registers at bytes 432 to 443, and the chaining value's address, the next
block's and the count of blocks left at 448, 452 and 456. It takes the
table's address (`symPush`), makes the rounds' keys from the schedule
(`keys`), and for each block exclusive-ors it with the chaining value into
the buffer's block, enciphers that in place, and stores it as the chaining
value.

The rounds' keys are made at fixed offsets from the buffer's address, 48
round keys one after another, with no pointer that moves: the analysis of
constant time then knows where each store goes and keeps what it knows of
the function's slots, which a store of a secret through an address it does
not know makes it forget. The block's store to the chaining value is such a
store, so the loop loads the three slots and `ebp`'s before it and stores
them back after it (as `update`'s loop does with its two).

`fin`, a run of `finalize` on registers (the key schedule and the subkeys
in `eax`, the chaining value's address in `edx`, the last bytes' in `ebx`,
their number in `esi`, the working space in `edi`), forms the last block
`Mₙ` at byte 464 of the working space and chains it with `chain`: `Mₙ* ⊕ K1`
for a whole block, else the bytes of `Mₙ*`, each copied by code of its own
(the number of bytes is public), `0x80` after them, zeros, and `K2`. It
keeps `ebx` and `esi` at bytes 472 and 476, and the two addresses at 480
and 484.

No address and no branch depends on the key, the state or the message, but
on their addresses and lengths.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.X86.Ssse3

open VG.X86
open VG.Impl.Modes.X86 (sb at_)
open VG.Impl.TripleDes.X86.Ssse3 (key crypt tableName keyOff blkOff)

/-- The internal function's name. -/
def chainName : String := "vg_cmac_triple_des_chain_ssse3"

/-! ## The working space's offsets -/

/-- `ebx`, `esi` and `ebp`, kept. -/
def oSave : Nat := 432
/-- The chaining value's address. -/
def oC : Nat := 448
/-- The next block's address. -/
def oD : Nat := 452
/-- The count of blocks left. -/
def oN : Nat := 456
/-- The last block `Mₙ`. -/
def oMn : Nat := 464
/-- `fin`'s `ebx` and `esi`, and the two addresses. -/
def oFin : Nat := 472

/-! ## A run of `update` -/

/-- The 48 rounds' keys in the order of use, from the schedule at `eax` to
the buffer at `esi`: round `t` of the first key, of the second in reverse,
and of the third. -/
def keys : List Instr :=
  (List.range 16).flatMap fun t =>
    key .eax (8 * t) (keyOff + 8 * t) ++ key .eax (248 - 8 * t) (keyOff + 128 + 8 * t) ++
      key .eax (256 + 8 * t) (keyOff + 256 + 8 * t)

/-- The registers and the run's arguments to their slots, and the schedule's
address to `ebp`. -/
def chainSave : List Instr :=
  [.store (at_ sb oSave) .ebx, .store (at_ sb (oSave + 4)) .esi, .store (at_ sb (oSave + 8)) .ebp,
   .store (at_ sb oC) .edx, .store (at_ sb oD) .ebx, .store (at_ sb oN) .esi, .mov .ebp (.reg .eax)]

/-- The table's address (in `eax`) to the buffer's first slot, and the
rounds' keys. -/
def chainKeys : List Instr :=
  ([.store (at_ sb 0) .eax, .mov .eax (.reg .ebp), .mov .esi (.reg sb)] : List Instr) ++ keys

/-- The chaining value exclusive-ored with the next block, to the buffer's
block. -/
def chainIn : List Instr :=
  [.mov .ecx (.mem (at_ sb oC)), .mov .esi (.mem (at_ sb oD)), .mov .eax (.mem (at_ .ecx 0)),
   .mov .edx (.mem (at_ .ecx 4)), .alu .xor .eax (.mem (at_ .esi 0)), .alu .xor .edx (.mem (at_ .esi 4)),
   .store (at_ sb blkOff) .eax, .store (at_ sb (blkOff + 4)) .edx]

/-- The buffer's block to the chaining value, and on to the next block: the
slots are loaded before the block is stored and stored back after it; ZF is
set after the last block. -/
def chainOut : List Instr :=
  [.mov .eax (.mem (at_ sb blkOff)), .mov .edx (.mem (at_ sb (blkOff + 4))), .mov .ecx (.mem (at_ sb oC)),
   .mov .esi (.mem (at_ sb oD)), .mov .ebp (.mem (at_ sb oN)), .mov .ebx (.mem (at_ sb (oSave + 8))),
   .store (at_ .ecx 0) .eax, .store (at_ .ecx 4) .edx, .alu .add .esi (.imm 8),
   .store (at_ sb oC) .ecx, .store (at_ sb oD) .esi, .store (at_ sb (oSave + 8)) .ebx,
   .alu .sub .ebp (.imm 1), .store (at_ sb oN) .ebp]

/-- A block. -/
def chainBody : Prog isa := .seq (.block chainIn) (.seq crypt (.block chainOut))

/-- The registers back. -/
def chainRestore : List Instr :=
  [.mov .ebx (.mem (at_ sb oSave)), .mov .esi (.mem (at_ sb (oSave + 4))), .mov .ebp (.mem (at_ sb (oSave + 8)))]

/-- The run's work once the registers are in their slots and the table's
address is in `eax`: the keys, the blocks, and the registers back. -/
def chainRun : Prog isa := .seq (.block chainKeys) (.seq (.loop chainBody .ne) (.block chainRestore))

/-- `vg_cmac_triple_des_chain_ssse3`: the chaining value at `edx` after the
`esi` blocks at `ebx`, under the key schedule at `eax`, with the working
space at `edi`. -/
def chain : Prog isa :=
  .seq (.block ([.alu .cmp .esi (.imm 0)] : List Instr))
    (.ite .e (.block [])
      (.seq (.block chainSave) (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) chainRun)))

/-- A run of `update`: the function's call. -/
def run : Prog isa := .call chainName chain

/-! ## A run of `finalize` -/

/-- The registers and the two addresses to their slots; ZF is set for a
whole last block. -/
def finSave : List Instr :=
  [.store (at_ sb oFin) .ebx, .store (at_ sb (oFin + 4)) .esi, .store (at_ sb (oFin + 8)) .eax,
   .store (at_ sb (oFin + 12)) .edx, .alu .cmp .esi (.imm 8)]

/-- `Mₙ = Mₙ* ⊕ K1` into `eax:edx`, for a whole last block. -/
def full : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .mov .edx (.mem (at_ .ebx 4)), .mov .ecx (.mem (at_ sb (oFin + 8))),
   .alu .xor .eax (.mem (at_ .ecx 384)), .alu .xor .edx (.mem (at_ .ecx 388))]

/-- Byte `i` of the last bytes to byte `i` of `Mₙ`'s slot, if there are more
than `i` of them. -/
def copyByte (i : Nat) : Prog isa :=
  .seq (.block ([.alu .cmp .esi (.imm (BitVec.ofNat 32 (i + 1)))] : List Instr))
    (.ite .b (.block []) (.block [.movzx8 .eax (at_ .ebx i), .store8 (at_ sb (oMn + i)) .al]))

/-- `0x80` after the bytes copied, and the slot exclusive-ored with `K2` into
`eax:edx`. -/
def padK2 : List Instr :=
  [.mov .ecx (.reg sb), .alu .add .ecx (.reg .esi), .mov .eax (.imm 0x80), .store8 (at_ .ecx oMn) .al,
   .mov .eax (.mem (at_ sb oMn)), .mov .edx (.mem (at_ sb (oMn + 4))), .mov .ecx (.mem (at_ sb (oFin + 8))),
   .alu .xor .eax (.mem (at_ .ecx 392)), .alu .xor .edx (.mem (at_ .ecx 396))]

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` into `eax:edx`, for fewer than eight last
bytes. -/
def partialBlock : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .store (at_ sb oMn) .eax, .store (at_ sb (oMn + 4)) .eax])
    (.seq (copyByte 0) (.seq (copyByte 1) (.seq (copyByte 2) (.seq (copyByte 3) (.seq (copyByte 4)
      (.seq (copyByte 5) (.seq (copyByte 6) (.block padK2))))))))

/-- `Mₙ` to its slot, and the arguments of the run that chains it. -/
def finArgs : List Instr :=
  [.store (at_ sb oMn) .eax, .store (at_ sb (oMn + 4)) .edx, .mov .eax (.mem (at_ sb (oFin + 8))),
   .mov .edx (.mem (at_ sb (oFin + 12))), .mov .ebx (.reg sb), .alu .add .ebx (.imm (BitVec.ofNat 32 oMn)),
   .mov .esi (.imm 1)]

/-- A run of `finalize`. -/
def fin : Prog isa :=
  .seq (.block finSave) (.seq (.ite .e (.block full) partialBlock)
    (.seq (.block finArgs) (.seq run
      (.block [.mov .ebx (.mem (at_ sb oFin)), .mov .esi (.mem (at_ sb (oFin + 4)))]))))

/-! ## The streaming functions -/

/-- `vg_cmac_triple_des_absorb_ssse3`, with its working space as an argument. -/
def absorb : Prog isa := Impl.CmacTripleDes.Stream.X86.absorbWith run

/-- `vg_cmac_triple_des_finish_ssse3`, with its working space as an argument. -/
def finish : Prog isa := Impl.CmacTripleDes.Stream.X86.finishWith fin

/-! ## The functions as emitted

Each function with its working space in a frame on the stack
(`withStackScratch`), of a size that puts the working space, and with it
the block function's two slots of sixteen bytes, at a multiple of sixteen
when `esp` was one at the call; then its cleanup
(`Impl.Scrub.X86.scrubAll rb W`): the `W` bytes of stack below `esp` that
its contract reserves zeroed, and the registers a callee may change
cleared, so that it returns without secret residue. -/

namespace Fn

/-- `Spec.Cmac.tdesAbsorbApi`'s function as emitted. -/
def absorb : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 752 (Impl.StackScratch.X86.withStackScratch 728 5 Ssse3.absorb)

/-- `Spec.Cmac.tdesFinishApi`'s function as emitted. -/
def finish : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 748 (Impl.StackScratch.X86.withStackScratch 724 4 Ssse3.finish)

end Fn

end VG.Impl.CmacTripleDes.X86.Ssse3
