module

public import VerifiedGarbage.Impl.Cast5.X86
public import VerifiedGarbage.Impl.Modes.X86.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# CAST5's core for the modes on x86 (32-bit)

`dirCore up`: the ECB code's block (`load`, `encryptBlock` or
`decryptBlock`, `Impl/Cast5/X86.lean`) as a core for the modes
(`Impl/Modes/X86/Seq.lean`), whose key is two arguments: the subkeys and the
number of rounds. Its slots: ECB's 256-byte working space (slots 0 to 63),
at the scratch buffer's base, and the buffer's one block (slots 64 and 65);
76 slots in all, with the modes' (`[u64; 38]`). `crypt` points `esi` at the
working space, writes the subkeys' address, the number of rounds and the
block's address to their slots there, from the stack arguments, and runs
the block; `edi`, which the rounds use, is the working space's address again
after it.

The block's output store goes through a pointer the analysis of constant
time does not know as a region's base, so it forgets what the scratch buffer
holds; `store` therefore reads the modes' data pointer and steps left
(`Core.dSlot`, `Core.nSlot`) before it and writes them back, unchanged,
after, as ECB's `store` does for its own slots.
-/

@[expose] public section

namespace VG.Impl.Cast5.X86.Modes

open VG.X86
open VG.Impl.Cast5.X86

/-- The buffer's block. -/
def bufSlot : Nat := 64

/-- The core's slots and the modes' data pointer and steps left. -/
def coreSlots : Nat := 66
def dSlot : Nat := coreSlots + 4
def nSlot : Nat := coreSlots + 5

/-- The working space (the scratch buffer, at `edi`) to `esi`, and the
subkeys' address, the number of rounds (the first two stack arguments) and
the block's address to their slots. -/
def setup : List Instr :=
  [.mov .esi (.reg .edi), .mov .eax (.mem (at_ .esp 4)), .store (at_ .esi schedOff) .eax,
   .mov .eax (.mem (at_ .esp 8)), .store (at_ .esi roundsOff) .eax,
   .mov .eax (.reg .esi), .alu .add .eax (imm (4 * bufSlot)), .store (at_ .esi dataOff) .eax]

/-- `(Rₙ, Lₙ)` to the block, the modes' data pointer and steps left read
before and written again after, and `edi` the working space's address. -/
def store : List Instr :=
  [.mov .edx (.mem (at_ .esi dataOff)), .mov .eax (.mem (at_ .esi (4 * dSlot))),
   .mov .ecx (.mem (at_ .esi (4 * nSlot))),
   .bswap .ebp, .store (at_ .edx 0) .ebp, .bswap .ebx, .store (at_ .edx 4) .ebx,
   .store (at_ .esi (4 * dSlot)) .eax, .store (at_ .esi (4 * nSlot)) .ecx, .mov .edi (.reg .esi)]

/-- The block, encrypted (`up`) or decrypted. -/
def crypt (up : Bool) : Prog isa :=
  .seq (.block setup) (.seq (.block load) (.seq (if up then encryptBlock else decryptBlock) (.block store)))

/-- CAST5's core for the modes, encrypting (`up`) or decrypting. -/
def dirCore (up : Bool) : Impl.Modes.X86.Core where
  prepare := .block []
  crypt := crypt up
  slots := coreSlots
  total := coreSlots + 10
  buf := bufSlot
  G := 1
  bw := 2
  stack := 4
  ka := 2

/-- `vg_cast5_cbc_encrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcEncryptChained : Prog isa := (dirCore true).seq (Impl.Modes.Mode.cbcEncChained 2)
/-- `vg_cast5_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore false).seq (Impl.Modes.Mode.cbcDecChained 2)
/-- `vg_cast5_ofb`. -/
def ofb : Prog isa := (dirCore true).seq (Impl.Modes.Mode.ofb 2)
/-- `vg_cast5_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore true).seq (Impl.Modes.Mode.cfbEnc 2)
/-- `vg_cast5_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore true).seq (Impl.Modes.Mode.cfbDec 2)

end VG.Impl.Cast5.X86.Modes
