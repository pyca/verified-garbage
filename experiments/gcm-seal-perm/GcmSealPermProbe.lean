import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Blocks

def lowMask : BitVec 128 := 0x08090a0b0c0d0e0f18191a1b1c1d1e1f
def highMask : BitVec 128 := 0x00010203040506071011121314151617

def maskCache : List Instr :=
 Impl.Aes.PPC64LE.Crypto.setMask U lowMask ++
 [.li .r11 32,.stxvd2x U .r16 .r11] ++
 Impl.Aes.PPC64LE.Crypto.setMask U highMask ++
 [.li .r11 48,.stxvd2x U .r16 .r11,.li .r11 80,.stxvd2x .v19 .r16 .r11,
  .li .r11 96,.stxvd2x .v13 .r16 .r11]

def productsPerm (a b : VReg) : List Instr :=
 [.vop (.perm T a b .v19),.vop (.perm U a b .v13),
  .vop (.pmsumd HI U .v9),.vop (.pmsumd LO T .v8),
  .vop (.pmsumd MID U .v8),.vop (.pmsumd U T .v9),.vop (.logic .xor MID MID U)]

def ghPairPerm (j : Nat) : List Instr :=
 ghInject j ++ ghRead ++ productsPerm (reg (2*j)) (reg (2*j+1)) ++ ghAcc j

def ghStartPerm : List Instr := [.lxvd2x .v19 .r16 .r21,.lxvd2x .v13 .r16 .r22] ++ ghStart

def ghCodePerm : List Instr := (List.range 4).flatMap ghPairPerm ++
 [.lxvd2x .v19 .r16 .r24,.lxvd2x .v13 .r16 .r18] ++ ghFinish

def batchPerm : Prog isa := .seq (.block (counters 8))
 (.seq aes8 (.block (stores ++ ghStartPerm ++ ghCodePerm)))

def codePerm : Prog isa := .ite (.zero .d .r7) (.block [])
 (.seq (.block (entryPrep ++ foldSetup ++ maskCache ++ entryFinish))
 (.seq cache (.seq (.loop batchPerm (.nonzero .d .r7)) (.block VG.Impl.AesGcm.PPC64LE.Blocks.exit))))

def encryptPerm : Prog isa := .ite (.zero .d .r8) (.block [])
 (.seq (.block wrapperEntry)
 (.seq (.ite (.zero .d .r12) (.block []) (.seq (.block bulkArgs) (.seq codePerm (.block bulkRest))))
 (.seq tail (.block wrapperExit))))

def fastBodyPerm : Prog isa :=
 .seq (.block Impl.AesGcm.PPC64LE.SealFused.blockArgs)
 (.seq (.call "vg_aes_gcm_encrypt_blocks_perm" encryptPerm)
 (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup)
 (.seq Impl.AesGcm.PPC64LE.cryptTail (.seq (Impl.AesGcm.PPC64LE.absorb 16) (Impl.AesGcm.PPC64LE.finTag 0)))))

def bodyPerm : Prog isa := .seq (.block [.lsr .d .r12 .r23 9])
 (.ite (.zero .d .r12) (.seq Impl.AesGcm.PPC64LE.oneCrypt (Impl.AesGcm.PPC64LE.oneTag 0)) fastBodyPerm)

def sealPerm : Prog isa := .seq (.block (Impl.AesGcm.PPC64LE.oneEntry 104))
 (.seq Impl.AesGcm.PPC64LE.oneAad (.seq bodyPerm (.seq (.block Impl.AesGcm.PPC64LE.tagOut) (.block Impl.AesGcm.PPC64LE.restore))))

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n"
 for (name,code) in [("seal_base",Impl.AesGcm.PPC64LE.«seal»),
     ("seal_fused",Impl.AesGcm.PPC64LE.SealFused.«seal»),("seal_perm",sealPerm),
     ("vg_aes_gcm_encrypt_blocks",encrypt),("vg_aes_gcm_encrypt_blocks_perm",encryptPerm),
     ("vg_aes_ctr32",Impl.Aes.PPC64LE.ctr32),("vg_ghash",Impl.Gcm.PPC64LE.ghash)] do
  asm := asm ++ s!".globl {name}\n.type {name},@function\n{name}:\n"
  for line in printer.function code do
   match line with
   | .text x => asm := asm ++ x ++ "\n"
   | .call name => asm := asm ++ printer.call ++ " " ++ name ++ "\n"
   | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/gcm-seal-perm.s" asm
