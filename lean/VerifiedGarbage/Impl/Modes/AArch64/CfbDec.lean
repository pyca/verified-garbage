module

public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-! # Batched CFB128 decryption for 16-byte block ciphers on AArch64

CFB decryption encrypts the preceding original ciphertext, or the initial IV.
Gather those independent inputs before any plaintext store. The mode's two
chaining slots keep the last original ciphertext across calls of the core.
The final ciphertext is copied to the caller's IV at entry, as in CBC
chained decryption, with no IV change for empty input.
-/

@[expose] public section
namespace VG.Impl.Modes.AArch64
open VG.AArch64 VG.Impl.Aes.AArch64
namespace Core
variable (c : Core)

def cfbDecGatherArgs : List Instr :=
 [.addImm .x .x14 sb (8*c.buf), .addImm .x .x14 .x14 16,
  movR .x15 c.dataReg, .subImm .x .x17 .x16 1]

/-- One input from the chain slots, then the group's preceding ciphertexts. -/
def cfbDecGather : Prog isa :=
 .seq (.block ((List.range 2).flatMap (copyW .x8 sb sb (8*c.buf) (8*c.hiSlot)) ++
    c.cfbDecGatherArgs))
  (.seq (.ite (.zero .x .x17) (.block []) c.copyBlocks)
    (.block ((List.range 2).flatMap (copyW .x8 sb .x15 (8*c.hiSlot) 0))))

def cfbDecGroup : Prog isa :=
 .seq c.groupCount (.seq c.cfbDecGather (.seq c.crypt
   (.seq c.groupCount (.seq (.block c.xorArgs)
     (.seq xorBlocks (.block c.advance))))))

def cfbDecryptBatched (r : CtrRegs) : Prog isa :=
 .seq (.block (c.ctrEntry r ++ c.cbcSetup r))
  (.seq (c.cbcLastToIv r)
   (.seq (.block (c.ctrArgs r))
    (.seq c.prepare
     (.seq (.ite (.zero .x c.leftReg) (.block [])
       (.loop c.cfbDecGroup (.nonzero .x c.leftReg))) (.block c.restoreRegs)))))

end Core
end VG.Impl.Modes.AArch64
