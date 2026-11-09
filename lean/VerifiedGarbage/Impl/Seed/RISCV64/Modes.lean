module

public import VerifiedGarbage.Impl.Modes.RISCV64.Shared
public import VerifiedGarbage.Impl.Modes.RISCV64.Wide
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Seed.RISCV64.Ecb

/-!
# SEED's modes on RISC-V

`inlineCore d g`: ECB's batch (`Ecb.lean`), inlined, as a core for the modes
(`Impl/Modes/RISCV64/Seq.lean`), on `g` blocks: ECB's
scratch buffer is the core's slots from `coreSlot` (`ecbOff` bytes into the
frame), and ECB's prologue (`prologue`) moves its base to `a5`, saves the
caller's `s0`–`s11` and builds `g16`'s masks; the `g` blocks of the core's
buffer (from slot `bufSlot`, after ECB's slots) are copied into lanes
`0`–`g - 1` of the arrays (ECB's copy loop), sixteen rounds run on every lane
(`rounds d`, the other lanes holding whatever they hold), and those lanes are
copied back,
under the schedule at `a0`, read in place, the round keys in the order of the
direction `d`: encryption's for CBC encryption, OFB and CFB, decryption's
for CBC decryption.

The rounds keep only `ra`, `a0`–`a3` and `a5`, and memory is secret to the
analysis of constant time, so the modes' state (`s1`–`s3`, which address
and count) waits in `a1`, `a2` and `ra` (`park`), `ra` itself in the core's
last slot (`raSlot`); the frame's base (`s4`) is ECB's base less `ecbOff`.
After the block, ECB's epilogue restores `s0`–`s11`, then the modes' state
and `ra` are put back (`coreOut`). `136 + 2 g` slots in all, with the
modes'.

`cbcEncryptChained`, `ofb` and `cfbEncrypt` (schedule = a0, iv = a1,
data = a2, n = a3), whose blocks each need the one before, are the modes over
the core on one block. `cbcDecryptChained` and `cfbDecrypt` take sixteen
blocks a step on the core on sixteen (`Core.seq2`, `Impl/Modes/RISCV64/Wide.lean`)
while sixteen are left, then one a step on the same core: the rounds cost the
same for any number of lanes.

`dirCore` wraps this body with named internal calls (`Core.shared`), so the
key preparation and batch code are emitted once across modes, alignment
branches, and wide and tail paths. Two additional slots preserve the
caller's return address and keep the frame aligned; the mode wipes them
with the original frame. The callee computes its own pointers after the
call, which may clobber all temporary registers.
-/

@[expose] public section

namespace VG.Impl.Seed.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64
open VG.Spec.Seed (Direction)

/-- ECB's scratch buffer: the core's slots, from `coreSlot`. -/
def ecbOff : Nat := 8 * Modes.RISCV64.coreSlot

/-- The core's buffer, after ECB's slots. -/
def bufSlot : Nat := Modes.RISCV64.coreSlot + scratchSlots

/-- Where `ra` waits during the block, after the buffer's `g` blocks, as an
offset from ECB's base. -/
def raOff (g : Nat) : Nat := 8 * (scratchSlots + 2 * g)

/-- The modes' state to `a1`, `a2` and `ra`, `ra` to its slot. -/
def park (g : Nat) : List Instr := [.store .d .ra sb (raOff g), movR .a1 .s1, movR .a2 .s2, movR .ra .s3]

/-- The key pointer at the first round's key; `g` blocks to copy, from the
buffer, into lanes `0`–`g - 1`. -/
def copyFrom (d : Direction) (g : Nat) : List Instr :=
  [.addi .a0 .a0 (keyStart d), .li t2 (g : Int), .addi .t3 sb ((8 * scratchSlots : Nat) : Int), movR .t4 sb]

/-- ECB's base and prologue, and the modes' state parked. -/
def coreIn (d : Direction) (g : Nat) : List Instr :=
  [.addi t0 Modes.RISCV64.sb ecbOff] ++ prologue t0 ++ park g ++ copyFrom d g

/-- `g` blocks to copy out, from lanes `0`–`g - 1` to the buffer. -/
def copyTo (g : Nat) : List Instr := [.li t2 (g : Int), .addi .t3 sb ((8 * scratchSlots : Nat) : Int), movR .t4 sb]

/-- The key pointer back, the caller's registers restored, the modes' state
and `ra` back, and the frame's base. -/
def coreOut (d : Direction) (g : Nat) : List Instr :=
  [.addi .a0 .a0 (-(keyStart d : Int))] ++ seedRestore ++
    [movR .s1 .a1, movR .s2 .a2, movR .s3 .ra, .load .d .ra sb (raOff g),
      .addi Modes.RISCV64.sb sb (-(ecbOff : Int))]

/-- The blocks: copied into the first `g` lanes, enciphered, and copied back. -/
def coreCrypt (d : Direction) (g : Nat) : Prog isa :=
  .seq (.block (coreIn d g)) (.seq (.loop (.block copyInBody) (.nonzero t2)) (.seq (rounds d)
    (.seq (.block (copyTo g)) (.seq (.loop (.block copyOutBody) (.nonzero t2)) (.block (coreOut d g))))))

/-- SEED's core for the modes, in the direction `d`, on `g` blocks (1 or 16). -/
def inlineCore (d : Direction) (g : Nat) : Modes.RISCV64.Core where
  prepare := .block []
  crypt := coreCrypt d g
  total := bufSlot + 1 + 2 * g
  buf := bufSlot
  G := g
  bw := 4

/-- Shared key preparation and batch encryption, with a saved return address. -/
def dirCore (d : Direction) (g : Nat) : Modes.RISCV64.Core :=
  (inlineCore d g).shared "vg_legacy_modes_prepare_empty"
    ("vg_seed_modes_crypt_" ++ (if d = .encrypt then "encrypt" else "decrypt") ++ "_" ++ (if g = 1 then "1" else "16"))

/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt 1).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa :=
  (dirCore .decrypt 16).seq2 (Modes.Mode.cbcDecWide 4 16) (Modes.Mode.cbcDecChained 4) 4

/-- `vg_seed_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt 1).seq (Modes.Mode.ofb 4)

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt 1).seq (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  (dirCore .encrypt 16).seq2 (Modes.Mode.cfbDecWide 4 16) (Modes.Mode.cfbDecEarly 4) 4

end VG.Impl.Seed.RISCV64
