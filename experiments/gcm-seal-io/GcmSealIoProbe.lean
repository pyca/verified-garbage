import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Blocks

def roundIO (i : Nat) : List Instr :=
 Impl.Aes.PPC64LE.Crypto.cipherRegs false false (roundKeyRegs.getD i .v18) (rs 8) ++
 (if i<8 then [.lxvd2x (dataReg i) .r6 (dataOffset i),
    .vop (.perm (dataReg i) (dataReg i) (dataReg i) .v19)] else [])

def rawIO (last : Bool) : List Instr := [.lxvd2x .v18 .r9 .r0] ++
 Impl.Aes.PPC64LE.Crypto.cipherRegs false last .v18 (rs 8)

def middleIO : List Instr := rawIO false ++
 [Impl.Aes.PPC64LE.Crypto.keyStep false,.subi .r10 .r10 1]

def aesIO : Prog isa :=
 .seq (.block (aesInitial ++ keyReads ++ (List.range 9).flatMap roundIO ++ aesRemaining))
  (.seq (.ite (.zero .d .r10) (.block []) (.loop (.block middleIO) (.nonzero .d .r10))) (.block (rawIO true)))

def storesIO : List Instr := (List.range 8).map (fun i => .vop (.logic .xor (reg i) (reg i) (dataReg i))) ++
 dataWrite ++ [.addi .r6 .r6 128,.subi .r7 .r7 8]

def batchIO : Prog isa := .seq (.block (counters 8)) (.seq aesIO (.block (storesIO ++ ghStart ++ ghCode)))

def codeIO : Prog isa := .ite (.zero .d .r7) (.block [])
 (.seq (.block entry) (.seq cache (.seq (.loop batchIO (.nonzero .d .r7)) (.block VG.Impl.AesGcm.PPC64LE.Blocks.exit))))

def encryptIO : Prog isa := .ite (.zero .d .r8) (.block [])
 (.seq (.block wrapperEntry)
 (.seq (.ite (.zero .d .r12) (.block []) (.seq (.block bulkArgs) (.seq codeIO (.block bulkRest))))
 (.seq tail (.block wrapperExit))))

def fastBodyIO : Prog isa :=
 .seq (.block Impl.AesGcm.PPC64LE.SealFused.blockArgs)
 (.seq (.call "vg_aes_gcm_encrypt_blocks_io" encryptIO)
 (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup)
 (.seq Impl.AesGcm.PPC64LE.cryptTail (.seq (Impl.AesGcm.PPC64LE.absorb 16) (Impl.AesGcm.PPC64LE.finTag 0)))))

def bodyIO : Prog isa := .seq (.block [.lsr .d .r12 .r23 9])
 (.ite (.zero .d .r12) (.seq Impl.AesGcm.PPC64LE.oneCrypt (Impl.AesGcm.PPC64LE.oneTag 0)) fastBodyIO)

def sealIO : Prog isa := .seq (.block (Impl.AesGcm.PPC64LE.oneEntry 104))
 (.seq Impl.AesGcm.PPC64LE.oneAad (.seq bodyIO (.seq (.block Impl.AesGcm.PPC64LE.tagOut) (.block Impl.AesGcm.PPC64LE.restore))))

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n"
 for (name,code) in [("seal_base",Impl.AesGcm.PPC64LE.«seal»),
     ("seal_fused",Impl.AesGcm.PPC64LE.SealFused.«seal»),("seal_io",sealIO),
     ("vg_aes_gcm_encrypt_blocks",encrypt),("vg_aes_gcm_encrypt_blocks_io",encryptIO),
     ("vg_aes_ctr32",Impl.Aes.PPC64LE.ctr32),("vg_ghash",Impl.Gcm.PPC64LE.ghash)] do
  asm := asm ++ s!".globl {name}\n.type {name},@function\n{name}:\n"
  for line in printer.function code do
   match line with
   | .text x => asm := asm ++ x ++ "\n"
   | .call name => asm := asm ++ printer.call ++ " " ++ name ++ "\n"
   | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/gcm-seal-io.s" asm
