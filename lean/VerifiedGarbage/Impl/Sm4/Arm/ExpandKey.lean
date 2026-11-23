module

public import VerifiedGarbage.Impl.Sm4.Arm.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# The SM4 key schedule on ARMv7

`expandKey(key = r0, schedule = r1, scratch = r2)`: `vg_sm4_expand_key`
with its working space in the scratch buffer (`Layers.lean`, moved to
`r8`), which the artifact allocates on the stack. As on x86-64
(`Impl/Sm4/X86_64/ExpandKey.lean`): the bitsliced rounds of ECB, with `L'`
for `L` and a table of `CK`'s planes for the round keys, run the key
schedule on eight copies of `MK ⊕ FK`; after every four rounds `fromBs`
puts the state's words in the tail buffer as a block, whose words
byte-reversed (`rev`) are the schedule's next 16 bytes. The schedule's
pointer is kept in slot `nSlot`.

Only the pointers, `kp`, the loop test, and the slot of the schedule's
pointer hold public values; no address and no branch depends on anything
else.

`vg_sm4_expand_key` (`expandKeyCall`) is a call of that code with its
working space on the stack, the internal `vg_sm4_expand_key_core`
(`keyCall`), which SM4-GCM's functions call too, in a frame saving `r4` and
`lr` (8 bytes, keeping the stack 8-byte aligned), with `lr` kept in `r4`
across the call, which preserves `r4`: so that the code is in the crate once.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Aes.Arm
open VG.Impl.Sm4 (Lin planeOf32 fkLE)

/-- Word `w` of the key, XOR `FK`, to the eight blocks of the tail buffer. -/
def loadKeyWord (w : Nat) : List Instr :=
  [.ldr t0 .r0 (4 * w)] ++ imm32 t1 (fkLE w) ++ [eorR t0 t0 t1] ++
  (List.range 8).map fun b => stS (tailAt b w) t0

def loadKey : List Instr := (List.range 4).flatMap loadKeyWord

/-- The planes of `CK`, in the table's slots. -/
def ckEntries : List (Nat × BitVec 32) :=
  (List.range 32).flatMap fun i => (List.range 8).map fun j => (tableSlot + 8 * i + j, planeOf32 (Spec.Sm4.ck i) j)

/-- The table of `CK`'s planes, through `t1`. -/
def ckTable : List Instr := ckEntries.flatMap fun (k, v) => imm32 t1 v ++ [stS k t1]

/-- The four new round keys, from the tail buffer's first block to the
schedule (whose pointer is in slot `nSlot`), the pointer stepped. -/
def extract : List Instr :=
  [ldS u7 nSlot] ++ (List.range 4).flatMap (fun k => [ldS t0 (tailAt 0 (3 - k)), .rev t0 t0, .str t0 u7 (4 * k)]) ++
  [.dp .add u7 u7 (.imm 16), stS nSlot u7]

/-- Four rounds of the key schedule, and their round keys to the schedule. -/
def keyBody : List Instr :=
  rounds4 .key ++ [.dp .add kp kp (.imm 128)] ++ fromBs ++ extract ++
  [.dp .sub t0 kp (.reg sb), .cmp t0 (.imm (BitVec.ofNat 32 (4 * tableEnd)))]

def expandKey : Prog isa :=
  .seq (.block (saveRegs .r2 ++ [movR sb .r2, stS nSlot .r1] ++ ckTable ++ loadKey ++ toBs ++ [kpAt tableSlot]))
    (.seq (.loop (.block keyBody) .ne) (.block ([movR .r12 sb] ++ restoreRegs .r12)))

/-- `vg_sm4_expand_key_core`: `expandKey` with its working space on the stack. -/
def keyCall : Prog isa :=
  .call (Spec.Sm4.expandKeyApi.name ++ "_core") (Impl.StackScratch.Arm.withRegScratch 1456 .r2 expandKey)

/-- `vg_sm4_expand_key`: a call of `vg_sm4_expand_key_core`, in a frame saving
`r4` and `lr`. -/
def expandKeyCall : Prog isa :=
  .frame (.push [.r4, .lr]) (.seq (.block [.mov .r4 (.reg .lr)]) (.seq keyCall (.block [.mov .lr (.reg .r4)])))
    (.pop .r4 8)

end VG.Impl.Sm4.Arm
