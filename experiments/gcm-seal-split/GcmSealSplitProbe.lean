import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Blocks
open VG.Impl.Aes.PPC64LE.Crypto (mov)

-- Experimental internal helper: r17/r19 carry source pointer/block count.
-- The outer seal saves r17 and restores r19 through its existing save area.
-- This prototype is not a verified artifact and is never emitted into Rust.
def sourceLoad : List Instr := (List.range 8).flatMap (fun i =>
 [.lxvd2x (dataReg i) .r17 (dataOffset i)])

def partialLoad (i : Nat) : Prog isa :=
 .seq (.block [.subi .r12 .r19 (i+1),.lsr .d .r12 .r12 63])
 (.ite (.zero .d .r12) (.block [.lxvd2x (dataReg i) .r17 (dataOffset i)])
   (.block [.lxvd2x (dataReg i) .r6 (dataOffset i)]))

def partialLoads : Prog isa :=
 ((List.range 8).map partialLoad).foldr Code.seq (.block [])

def splitLoad : Prog isa :=
 .ite (.zero .d .r19) (.block dataLoad)
 (.seq (.block [.lsr .d .r12 .r19 3])
 (.ite (.nonzero .d .r12)
   (.block (sourceLoad ++ [.addi .r17 .r17 128,.subi .r19 .r19 8]))
   (.seq partialLoads (.block [.lsl .r12 .r19 4,.add .r17 .r17 .r12,.li .r19 0]))))

def splitStores : Prog isa := .seq splitLoad
 (.block (dataMix ++ dataWrite ++ [.addi .r6 .r6 128,.subi .r7 .r7 8] ++ ghStart ++ ghCode))

def splitBatch : Prog isa := .seq (.block (counters 8)) (.seq aes8 splitStores)

def splitCore : Prog isa := .ite (.zero .d .r7) (.block [])
 (.seq (.block entry) (.seq cache
 (.seq (.loop splitBatch (.nonzero .d .r7)) (.block VG.Impl.AesGcm.PPC64LE.Blocks.exit))))

def copyPrefix : Prog isa := .ite (.zero .d .r19) (.block [])
 (.seq (.block [mov .r11 .r30,.li .r0 0])
 (.loop (.block [.lxvd2x U .r17 .r0,.stxvd2x U .r11 .r0,
  .addi .r17 .r17 16,.addi .r11 .r11 16,.subi .r19 .r19 1]) (.nonzero .d .r19)))

def splitEncrypt : Prog isa := .ite (.zero .d .r8) (.block [])
 (.seq (.block wrapperEntry)
 (.seq (.ite (.zero .d .r12) (.block [])
   (.seq (.block bulkArgs) (.seq splitCore (.block bulkRest))))
 (.seq copyPrefix (.seq tail (.block wrapperExit)))))

def splitFastBody : Prog isa := .seq (.block Impl.AesGcm.PPC64LE.SealFused.blockArgs)
 (.seq (.call "vg_gcm_split_probe" splitEncrypt)
 (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup)
 (.seq Impl.AesGcm.PPC64LE.cryptTail
 (.seq (Impl.AesGcm.PPC64LE.absorb 16) (Impl.AesGcm.PPC64LE.finTag 0)))))

def smallPrefix : Prog isa := .seq (.block [mov .r30 .r27])
 (.seq copyPrefix (.seq (.block [.addi .r30 .r31 16])
 (.seq Impl.AesGcm.PPC64LE.oneCrypt (Impl.AesGcm.PPC64LE.oneTag 0))))

def splitBody : Prog isa :=
 .seq (.block [.store .d .r17 .r31 112,.addSp .r12 0,.load .d .r17 .r12 112,
  .load .d .r19 .r12 120,.lsr .d .r12 .r23 9])
 (.seq (.ite (.zero .d .r12) smallPrefix splitFastBody)
 (.block [.load .d .r17 .r31 112]))

def sealSplit : Prog isa := Impl.AesGcm.PPC64LE.sealWith splitBody

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n"
 for (name,code) in [("seal_base",Impl.AesGcm.PPC64LE.SealFused.seal),
     ("seal_split_probe",sealSplit),("vg_gcm_split_probe",splitEncrypt),
     ("vg_aes_gcm_encrypt_blocks",encrypt),
     ("vg_aes_ctr32",Impl.Aes.PPC64LE.ctr32),("vg_ghash",Impl.Gcm.PPC64LE.ghash)] do
  asm := asm ++ s!".globl {name}\n.type {name},@function\n{name}:\n"
  for line in printer.function code do
   match line with
   | .text x => asm := asm ++ x ++ "\n"
   | .call name => asm := asm ++ printer.call ++ " " ++ name ++ "\n"
   | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/gcm-seal-split.s" asm
