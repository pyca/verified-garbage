module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
public import VerifiedGarbage.Impl.Modes.AArch64.Cfb8
public import VerifiedGarbage.Impl.Modes.AArch64.CfbDec

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on AArch64

`ofb`, `cfbEncrypt`, `cfb8Encrypt` and `cfb8Decrypt`
(schedule = x0, iv = x1, data = x2, n = x3, scratch = x4): the modes'
generic OFB, CFB and CFB8 (`Impl/Modes/AArch64/Fb.lean`, `Cfb8.lean`) over
the table core (`tableCore`, `Cbc.lean`: CMAC's block, one 8-byte block at
a time), with the working space in the scratch buffer, which the artifact
allocates on the stack, and the IV's address in `x28`, which the block
never writes.

`cfbDecrypt`, with the same arguments: the modes' batched CFB decryption
(`Impl/Modes/AArch64/CfbDec.lean`), whose blocks need no block's result for
the next, over the batched core for encryption (`batchCore .encrypt`,
`Cbc.lean`): each group of up to 128 blocks by one bitsliced batch.
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64

/-- The registers of the arguments. -/
def fbRegs : Impl.Modes.AArch64.CtrRegs := ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_triple_des_ofb`. -/
def ofb : Prog isa := tableCore.fb .ofb fbRegs .x28

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := tableCore.fb .cfbEnc fbRegs .x28

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (batchCore .encrypt).cfbDecryptBatched fbRegs

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := tableCore.cfb8 true fbRegs .x28

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := tableCore.cfb8 false fbRegs .x28

end VG.Impl.TripleDes.AArch64
