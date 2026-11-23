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

/-- `(Rₙ, Lₙ)` to the block, the modes' data pointer and steps left (the
slots 4 and 5 after a core's `cs`) read before and written again after, and
`edi` the working space's address. -/
def storeAt (cs : Nat) : List Instr :=
  [.mov .edx (.mem (at_ .esi dataOff)), .mov .eax (.mem (at_ .esi (4 * (cs + 4)))),
   .mov .ecx (.mem (at_ .esi (4 * (cs + 5)))),
   .bswap .ebp, .store (at_ .edx 0) .ebp, .bswap .ebx, .store (at_ .edx 4) .ebx,
   .store (at_ .esi (4 * (cs + 4))) .eax, .store (at_ .esi (4 * (cs + 5))) .ecx, .mov .edi (.reg .esi)]

def store : List Instr := storeAt coreSlots

/-- The block, encrypted (`up`) or decrypted, over the look-up `lk`
(`roundWith`), for a core of `cs` slots. -/
def cryptWith (lk : Prog isa) (cs : Nat) (up : Bool) : Prog isa :=
  .seq (.block setup) (.seq (.block load)
    (.seq (if up then encryptBlockWith lk else decryptBlockWith lk) (.block (storeAt cs))))

/-- The block, encrypted (`up`) or decrypted. -/
def crypt (up : Bool) : Prog isa := cryptWith (scan s1234Sym) coreSlots up

/-- CAST5's core for the modes over the look-up `lk`, which uses `stack`
bytes of stack: `cs` slots, of which the first 66 are the working space of
the rounds and the buffer's block. -/
def coreWith (lk : Prog isa) (cs stack : Nat) (up : Bool) : Impl.Modes.X86.Core where
  prepare := .block []
  crypt := cryptWith lk cs up
  slots := cs
  total := cs + 10
  buf := bufSlot
  G := 1
  bw := 2
  stack := stack
  ka := 2

/-- CAST5's core for the modes, encrypting (`up`) or decrypting. -/
def dirCore (up : Bool) : Impl.Modes.X86.Core := coreWith (scan s1234Sym) coreSlots 4 up

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
