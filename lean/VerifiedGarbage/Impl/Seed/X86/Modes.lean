module

public import VerifiedGarbage.Impl.Seed.X86.Ecb
public import VerifiedGarbage.Impl.Modes.X86.Wide
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# SEED's core for the modes on x86 (32-bit)

`dirCore d`: the core for the modes (`Impl/Modes/X86/Seq.lean`), with the
round keys in the order of the direction `d`: encryption's for CBC
encryption, OFB and CFB128, decryption's for CBC decryption. `crypt` calls
`vg_seed_encrypt_blocks` or `vg_seed_decrypt_blocks` (`Ecb.lean`) on the
buffer's eight blocks, a group of the function's, which it enciphers in one
pass, with the schedule (the first stack argument) and the working space,
the scratch buffer's first 244 slots (`modeWs`: the functions use 206 of
theirs, `slots`); `prepare` does nothing. The core's slots are those 244
and the buffer's 32 (`bufSlot`), then the modes' ten: 286 in all
(`[u64; 143]`).

CBC and CFB128 decryption, whose blocks can be deciphered independently,
take the blocks in groups (`Impl/Modes/X86/Wide.lean`): of eight while
eight are left, then of four and of two (`levels`), then one, each group
one call of the blocks function, whose pass costs the same for any number
of the buffer's blocks. The other modes, whose blocks each need the one
before, call it once a block.

The call's four arguments are pushed in a frame (20 bytes of stack with the
return address). The blocks function restores the callee-saved registers,
and keeps `esi` and `ebp` as public as they were for the analysis of
constant time (it stores only at known offsets of its working space between
its copy in and its copy out), but not `edi`, nor what the scratch buffer
holds: so the modes' data pointer and steps left wait in `esi` and `ebp`
and go back to their slots after the call, and `sb` comes back from the
scratch buffer's stack argument.
-/

@[expose] public section

namespace VG.Impl.Seed.X86

open VG.X86 VG.Impl.Aes.X86
open VG.Spec.Seed (Direction)

/-- The working space the modes give the blocks functions, in slots: the
functions' `slots` and the room the scratch buffer has left. -/
def modeWs : Nat := 244

/-- The buffer's eight blocks, after the blocks functions' working space. -/
def bufSlot : Nat := modeWs

/-- The core's slots: the working space and the buffer. -/
def coreSlots : Nat := bufSlot + 32

/-- The modes' data pointer and steps left (`Core.dSlot`, `Core.nSlot`). -/
def modeDSlot : Nat := coreSlots + 4
def modeNSlot : Nat := coreSlots + 5

/-- Before the call: the modes' data pointer and steps left to `esi` and
`ebp`, and the arguments: the schedule, the buffer, its eight blocks, and
the working space. -/
def callHead : List Instr :=
  [movS .esi modeDSlot, movS .ebp modeNSlot, .mov .eax (.mem (argOp 0)), movR .ecx sb,
   addI .ecx (BitVec.ofNat 32 (4 * bufSlot)), movI .edx 8]

/-- After the call: `sb` from the scratch buffer's argument, and the data
pointer and steps left back to their slots. -/
def callTail : List Instr := [.mov sb (.mem (argOp 4)), st modeDSlot .esi, st modeNSlot .ebp]

/-- The buffer's blocks through the blocks function of the direction `d`. -/
def cryptCall (d : Direction) : Prog isa :=
  .seq (.block callHead) (.seq (.frame (.push [.edi, .edx, .ecx, .eax]) (blocksCall d) (.pop .eax 4))
    (.block callTail))

/-- SEED's core for the direction `d`. -/
def dirCore (d : Direction) : Modes.X86.Core where
  prepare := .block []
  crypt := cryptCall d
  slots := coreSlots
  total := coreSlots + 10
  buf := bufSlot
  G := 8
  bw := 4
  stack := 20

/-- The sizes of the groups of blocks the modes whose blocks are independent
take, in turn, before single blocks. -/
def levels : List Nat := [8, 4, 2]

/-- `vg_seed_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_seed_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa :=
  (dirCore .decrypt).seqLevels (Modes.Mode.cbcDecWide 4) levels (Modes.Mode.cbcDecChained 4)

/-- `vg_seed_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_seed_cfb128_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa :=
  (dirCore .encrypt).seqLevels (Modes.Mode.cfbDecWide 4) levels (Modes.Mode.cfbDecEarly 4)

end VG.Impl.Seed.X86
