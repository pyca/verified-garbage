import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n"
 for (name,code) in [("seal_base",Impl.AesGcm.PPC64LE.«seal»),
     ("seal_fused",Impl.AesGcm.PPC64LE.SealFused.«seal»),
     ("vg_aes_gcm_encrypt_blocks",Impl.AesGcm.PPC64LE.Blocks.encrypt),
     ("vg_aes_ctr32",Impl.Aes.PPC64LE.ctr32),("vg_ghash",Impl.Gcm.PPC64LE.ghash)] do
  asm := asm ++ s!".globl {name}\n.type {name},@function\n{name}:\n"
  for line in printer.function code do
   match line with
   | .text x => asm := asm ++ x ++ "\n"
   | .call name => asm := asm ++ printer.call ++ " " ++ name ++ "\n"
   | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/gcm-seal-fused.s" asm
