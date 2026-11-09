module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block

/-!
# Triple DES's block functions, called by the modes on PPC64LE

`blockCall d` calls the block function of the direction `d`, on the block at
`r4` with the schedule at `r3` and its working space at `r5`, as the modes
(`Modes.lean`) and CMAC do. ECB itself is bitsliced (`Bitsliced.lean`).
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE.Ecb

open VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)

def blockCall (d : Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_triple_des_encrypt_block" encryptBlock
  | .decrypt => .call "vg_triple_des_decrypt_block" decryptBlock

end VG.Impl.TripleDes.PPC64LE.Ecb
