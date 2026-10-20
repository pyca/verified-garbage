module

public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Impl.Modes.X86.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# Blowfish's core for the modes on x86 (32-bit)

`dirCore up`: ECB's block (`Impl/Blowfish/X86.lean`) as a core for the
modes (`Impl/Modes/X86/Seq.lean`), whose key is the schedule (the first stack
argument), read in place: the block function reads the schedule's address
from its stack argument at every round, and `prepare` has nothing to do. Its
slots: ECB's 40-byte working space (slots 0 to 9), at the scratch buffer's
base, then the buffer's one block (slots 10 and 11); 22 slots in all, with
the modes' (`[u64; 11]`).

`crypt` points `ebp` at the scratch buffer, writes the buffer's address to
ECB's data pointer and loads the block into the halves (`loadBlock`), runs
the block function, encrypting (`up`) or decrypting, and stores the halves
back to the buffer through `ebp` (rather than through the data pointer, as
ECB's `storeBlock` does: the analysis of constant time then knows the stores
are in the scratch buffer, and keeps what it knows of the rest of it, the
modes' data pointer and steps left); `edi` is the scratch buffer's address
again after it.

CBC runs in the core's direction; OFB and CFB64 run the cipher forwards
(encryption) in both directions.
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86

open VG.X86

/-- The buffer's block, in bytes from the scratch buffer's base. -/
def bufOff : Nat := 40

/-- `ebp` the scratch buffer, and the buffer's address to the data pointer. -/
def modeSetup : List Instr :=
  [.mov .ebp (.reg .edi), .mov .ebx (.reg .ebp), .alu .add .ebx (imm bufOff), .store (at_ .ebp ptrOff) .ebx]

/-- The halves to the buffer, as big-endian words, through `ebp`; then `edi`
the scratch buffer's address again. -/
def modeStore : List Instr :=
  [.mov .eax (.mem (at_ .ebp xlOff)), .bswap .eax, .store (at_ .ebp bufOff) .eax,
   .mov .eax (.mem (at_ .ebp xrOff)), .bswap .eax, .store (at_ .ebp (bufOff + 4)) .eax, .mov .edi (.reg .ebp)]

/-- The buffer's block, encrypted (`up`) or decrypted. -/
def modeCrypt (up : Bool) : Prog isa :=
  .seq (.block (modeSetup ++ loadBlock)) (.seq (cipher 4 up) (.block modeStore))

/-- Blowfish's core for the modes, encrypting (`up`) or decrypting. -/
def dirCore (up : Bool) : Modes.X86.Core where
  prepare := .block []
  crypt := modeCrypt up
  slots := 12
  total := 22
  buf := 10
  G := 1
  bw := 2

/-- `vg_blowfish_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore true).seq (Modes.Mode.cbcEncChained 2)
/-- `vg_blowfish_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore false).seq (Modes.Mode.cbcDecChained 2)
/-- `vg_blowfish_ofb`. -/
def ofb : Prog isa := (dirCore true).seq (Modes.Mode.ofb 2)
/-- `vg_blowfish_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore true).seq (Modes.Mode.cfbEnc 2)
/-- `vg_blowfish_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore true).seq (Modes.Mode.cfbDec 2)

end VG.Impl.Blowfish.X86
