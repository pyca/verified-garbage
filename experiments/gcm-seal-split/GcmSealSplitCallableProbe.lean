import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.Impl.AesGcm.PPC64LE.SplitBlocks
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto (mov)

-- Experimental full-seal composition around the verified nine-argument helper.
-- The probe keeps its earlier twelve-argument C interface for identical inputs.
-- This enclosing seal is not a verified artifact and is never emitted into Rust.
def splitArgs : List Instr :=
 [.addSp .r12 0,.load .d .r0 .r12 96,.store .d .r0 .r31 256,
  .addi .r0 .r31 448,.store .d .r0 .r12 96,
  mov .r3 .r29,mov .r4 .r28,.addi .r5 .r30 48,.addi .r6 .r30 16,
  .load .d .r7 .r12 112,.load .d .r8 .r12 120,
  mov .r9 .r27,.lsr .d .r10 .r23 4]

def restoreArg : List Instr :=
 [.addSp .r12 0,.load .d .r0 .r31 256,.store .d .r0 .r12 96]

def splitBody : Prog isa := .seq (.block splitArgs)
 (.seq (.call "vg_aes_gcm_encrypt_blocks_split" Impl.AesGcm.PPC64LE.SplitBlocks.encrypt)
 (.seq (.block restoreArg)
 (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup)
 (.seq Impl.AesGcm.PPC64LE.cryptTail
 (.seq (Impl.AesGcm.PPC64LE.absorb 16) (Impl.AesGcm.PPC64LE.finTag 0))))))

def sealSplit : Prog isa := Impl.AesGcm.PPC64LE.sealWith splitBody

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n"
 for (name,code) in [("seal_base",Impl.AesGcm.PPC64LE.SealFused.seal),
     ("seal_split_probe",sealSplit),
     ("vg_aes_gcm_encrypt_blocks_split",Impl.AesGcm.PPC64LE.SplitBlocks.encrypt),
     ("vg_aes_gcm_encrypt_blocks",Impl.AesGcm.PPC64LE.Blocks.encrypt),
     ("vg_aes_ctr32",Impl.Aes.PPC64LE.ctr32),("vg_ghash",Impl.Gcm.PPC64LE.ghash)] do
  asm := asm ++ s!".globl {name}\n.type {name},@function\n{name}:\n"
  for line in printer.function code do
   match line with
   | .text x => asm := asm ++ x ++ "\n"
   | .call name => asm := asm ++ printer.call ++ " " ++ name ++ "\n"
   | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/gcm-seal-split-callable.s" asm
