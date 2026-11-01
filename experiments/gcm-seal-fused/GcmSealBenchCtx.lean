import VerifiedGarbage.Spec.Gcm
open VG

def main : IO Unit := do
 let mut out := ByteArray.empty
 for keyLen in [16,24,32] do
  let key : List Byte := List.replicate keyLen (0x24 : BitVec 8)
  let nr := Spec.Aes.rounds (keyLen/4)
  let w := Spec.Aes.expandKey key
  let h := Spec.Gcm.aesWith nr w 0
  for b in w ++ List.replicate (240-w.length) 0 ++ Spec.Gcm.toBytes h do out := out.push b.toNat.toUInt8
 IO.FS.writeBinFile "/workspace/scratch/gcm-seal-bench-ctx.bin" out
