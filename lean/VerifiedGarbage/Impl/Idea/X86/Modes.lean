module

public import VerifiedGarbage.Impl.Idea.X86
public import VerifiedGarbage.Impl.Modes.X86.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# IDEA's core for the modes on x86 (32-bit)

`modeCore`: ECB's block (`Impl/Idea/X86.lean`) as a core for the modes
(`Impl/Modes/X86/Seq.lean`), whose key is the schedule (the first stack
argument). Its slots: ECB's working space (slots 0 to 32: the copy of the
subkeys, `t₀`, the block's address), at the scratch buffer's base, then the
buffer's one block (slots 33 and 34); 46 slots in all, with the modes'
(`[u64; 23]`).

`prepare` copies the subkeys to the scratch buffer, as ECB's prologue does.
`crypt` points `esi` at the scratch buffer, writes the buffer's address to
ECB's `dataSlot`, and runs ECB's block (`load`, the eight rounds and the
output transformation), but stores the output words through `esi`, at the
buffer's offset, rather than through the address it loaded: the analysis of
constant time then knows the stores are in the scratch buffer, and keeps
what it knows of the rest of it (the modes' data pointer and steps left);
`edi` is the scratch buffer's address again after it.

IDEA decrypts with the same block function under the inverse schedule
(`vg_idea_invert_key`), so one core serves every mode in both directions.
-/

@[expose] public section

namespace VG.Impl.Idea.X86

open VG.X86

/-- The buffer's block. -/
def bufSlot : Nat := slots

/-- The core's slots. -/
def coreSlots : Nat := bufSlot + 2

/-- `esi` the scratch buffer, `edx` the schedule, and the subkeys copied. -/
def modePrepare : List Instr :=
  [.mov .esi (.reg .edi), .mov .edx (.mem (argOp 0))] ++ (List.range 26).flatMap copyWord

/-- `esi` the scratch buffer, and the buffer's address to `dataSlot`. -/
def modeSetup : List Instr :=
  [.mov .esi (.reg .edi), .mov .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 (4 * bufSlot))),
   .store (at_ .esi dataSlot) .eax]

/-- `ebx, edi, ecx, ebp` (`Y₁ … Y₄`) to the buffer, through `esi`, as `store`
does through `eax`; then `edi` the scratch buffer's address again. -/
def modeStore : List Instr :=
  [.shift .ror .ebx 16, .alu .or .ebx (.reg .edi), .bswap .ebx, .store (at_ .esi (4 * bufSlot)) .ebx,
   .shift .ror .ecx 16, .alu .or .ecx (.reg .ebp), .bswap .ecx, .store (at_ .esi (4 * bufSlot + 4)) .ecx,
   .mov .edi (.reg .esi)]

/-- The buffer's block, encrypted under the subkeys in the scratch buffer. -/
def modeCrypt : List Instr :=
  modeSetup ++ load ++ (List.range 8).flatMap round ++ output ++ modeStore

/-- IDEA's core for the modes. -/
def modeCore : Modes.X86.Core where
  prepare := .block modePrepare
  crypt := .block modeCrypt
  slots := coreSlots
  total := coreSlots + 11
  buf := bufSlot
  G := 1
  bw := 2

/-- `vg_idea_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := modeCore.seq (Modes.Mode.cbcEncChained 2)
/-- `vg_idea_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := modeCore.seq (Modes.Mode.cbcDecChained 2)
/-- `vg_idea_ofb`. -/
def ofb : Prog isa := modeCore.seq (Modes.Mode.ofb 2)
/-- `vg_idea_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := modeCore.seq (Modes.Mode.cfbEnc 2)
/-- `vg_idea_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := modeCore.seq (Modes.Mode.cfbDec 2)

end VG.Impl.Idea.X86
