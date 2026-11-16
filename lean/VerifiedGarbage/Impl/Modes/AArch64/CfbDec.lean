module

public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-! # Batched CFB decryption on AArch64, for any block cipher with blocks of 8 or 16 bytes

CFB decryption encrypts the preceding original ciphertext, or the initial IV.
Gather those independent inputs before any plaintext store. The mode's
chaining slots keep the last original ciphertext across calls of the core.
The final ciphertext is copied to the caller's IV at entry, as in CBC
chained decryption, with no IV change for empty input. Blocks are `bw`
8-byte words, as in CBC decryption (`Cbc.lean`).
-/

@[expose] public section
namespace VG.Impl.Modes.AArch64
open VG.AArch64 VG.Impl.Aes.AArch64
namespace Core
variable (c : Core)

def cfbDecGatherArgs : List Instr :=
 [.addImm .x .x14 sb (8*c.buf), .addImm .x .x14 .x14 (8*c.bw),
  movR .x15 c.dataReg, .subImm .x .x17 .x16 1]

/-- One input from the chain slots, then the group's preceding ciphertexts. -/
def cfbDecGather : Prog isa :=
 .seq (.block ((List.range c.bw).flatMap (copyW .x8 sb sb (8*c.buf) (8*c.hiSlot)) ++
    c.cfbDecGatherArgs))
  (.seq (.ite (.zero .x .x17) (.block []) c.copyBlocks)
    (.block ((List.range c.bw).flatMap (copyW .x8 sb .x15 (8*c.hiSlot) 0))))

/-- XOR `x17` blocks of `bw` words at `x14` into the blocks at `x15` (through
`x8`, `x9`): `xorBlocks` (`Ctr.lean`), for blocks of two words. -/
def xorBlocksW : Prog isa :=
  .loop (.block ((List.range c.bw).flatMap (fun w =>
      [.ldr .x .x8 .x14 (8 * w), .ldr .x .x9 .x15 (8 * w), eorR .x8 .x8 .x9, .str .x .x8 .x15 (8 * w)]) ++
    c.nextBlock)) (.nonzero .x .x17)

def cfbDecGroup : Prog isa :=
 .seq c.groupCount (.seq c.cfbDecGather (.seq c.crypt
   (.seq c.groupCount (.seq (.block c.xorArgs)
     (.seq c.xorBlocksW (.block c.advance))))))

def cfbDecryptBatched (r : CtrRegs) : Prog isa :=
 .seq (.block (c.ctrEntry r ++ c.cbcSetup r))
  (.seq (c.cbcLastToIv r)
   (.seq (.block (c.ctrArgs r))
    (.seq c.prepare
     (.seq (.ite (.zero .x c.leftReg) (.block [])
       (.loop c.cfbDecGroup (.nonzero .x c.leftReg))) (.block c.restoreRegs)))))

end Core
end VG.Impl.Modes.AArch64
