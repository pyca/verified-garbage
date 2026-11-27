module

public import VerifiedGarbage.Impl.Sm4.X86.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# The SM4 key schedule on x86 (32-bit)

`expandKey(key, schedule, scratch)`, cdecl: `vg_sm4_expand_key` with its
working space in the scratch buffer (`Layers.lean`, at `edi`), which the
artifact allocates on the stack. As on ARMv7
(`Impl/Sm4/Arm/ExpandKey.lean`): the bitsliced rounds of ECB, with `L'` for
`L` and a table of `CK`'s planes for the round keys, run the key schedule
on eight copies of `MK ⊕ FK`; after every four rounds `fromBs` puts the
state's words in the tail buffer as a block, whose words byte-reversed
(`bswap`) are the schedule's next 16 bytes. The schedule's pointer is kept
in slot `nSlot`, stored again after the stores through it.

Only the pointers, `kp`, the loop test, and the slot of the schedule's
pointer hold public values; no address and no branch depends on anything
else.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86

open VG.X86 VG.Impl.Aes.X86
open VG.Impl.Sm4 (planeOf32 fkLE)

/-- The planes of `CK`, in the table's slots. -/
def ckEntries : List (Nat × BitVec 32) :=
  (List.range 32).flatMap fun i => (List.range 8).map fun j => (tableSlot + 8 * i + j, planeOf32 (Spec.Sm4.ck i) j)

/-- The table of `CK`'s planes, through `eax`. -/
def ckTable : List Instr := ckEntries.flatMap fun (k, v) => [movI .eax v, st k .eax]

/-- Word `w` of the key (at `ecx`), XOR `FK`, to the eight blocks of the
tail buffer. -/
def loadKeyWord (w : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ecx (4 * w))), .alu .xor .eax (.imm (fkLE w))] ++
  (List.range 8).map fun b => st (tailAt b w) .eax

def loadKey : List Instr := [.mov .ecx (.mem (argOp 0))] ++ (List.range 4).flatMap loadKeyWord

/-- The four new round keys, from the tail buffer's first block to the
schedule (whose pointer is in slot `nSlot`), the pointer stepped and stored
back. -/
def extract : List Instr :=
  [movS .ecx nSlot] ++
  (List.range 4).flatMap (fun k => [movS .eax (tailAt 0 (3 - k)), .bswap .eax, .store (at_ .ecx (4 * k)) .eax]) ++
  [addI .ecx 16, st nSlot .ecx]

/-- Four rounds of the key schedule, and their round keys to the schedule. -/
def keyBody : List Instr :=
  rounds4 .key ++ [addI kp 128] ++ fromBs ++ extract ++
  [movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm (BitVec.ofNat 32 (4 * tableEnd)))]

def expandKey : Prog isa :=
  .seq (.block (saveRegs 2 ++ [.mov .eax (.mem (argOp 1)), st nSlot .eax] ++ ckTable ++ loadKey ++ toBs ++
      kpAt tableSlot))
    (.seq (.loop (.block keyBody) .ne) (.block restoreRegs))

/-- Call the shared key schedule with its scratch buffer in the existing
1448-byte stack budget. The return address occupies the old unused word;
the arguments and buffer have the same addresses at callee entry. -/
def expandKeyFramed : Prog isa :=
  .frame (.alloc 1444)
    (.seq (.block [
      .mov .eax (.mem ⟨.esp, 1448⟩), .store ⟨.esp, 0⟩ .eax,
      .mov .eax (.mem ⟨.esp, 1452⟩), .store ⟨.esp, 4⟩ .eax,
      .mov .eax (.reg .esp), .alu .add .eax (.imm 12), .store ⟨.esp, 8⟩ .eax])
      (.seq (.call "vg_sm4_expand_key_shared" expandKey)
        (.block (Impl.StackScratch.X86.wipe 12 358)))) (.free 1444)

/-- Clear the call header with the zero SIMD register left by the scratch wipe. -/
def expandKeyClean : Prog isa :=
  .seq expandKeyFramed
    (.frame (.alloc 1448) (.block [.movdquStore ⟨.esp, 0⟩ .xmm0]) (.free 1448))

end VG.Impl.Sm4.X86
