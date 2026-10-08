import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR
import VerifiedGarbage.Impl.Aes.X86_64.VaesZH

/-! # Prepared AVX-512 GCM with AES keys cached across batches -/

namespace VG.Impl.Gcm.X86_64.StitchZH
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ xorDataZ)
open VG.Impl.Gcm.X86_64.StitchZ (gq gq48 lastG adv)
open VG.Impl.Gcm.X86_64.StitchZR (setupP powP48)

def batch (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsZ .xmm14 .xmm0 .xmm15 aregs))
    (.seq (Aes.X86_64.VaesZH.aes aregs g) (.block (xorDataZ .xmm13 .rdx aregs j)))

def first : Prog isa := batch 0 fun _ => []

def body : Prog isa :=
  .seq (batch 4 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])

def body48 : Prog isa :=
  .seq (batch 12 (gq48 0)) (.seq (batch 16 (gq48 1)) (.seq (batch 20 (gq48 2))
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 96)])))

def dbody : Prog isa :=
  .seq (batch 0 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)])

def dbody48 : Prog isa :=
  .seq (batch 0 (gq48 0)) (.seq (batch 4 (gq48 1)) (.seq (batch 8 (gq48 2))
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 48)])))

def bigP : Prog isa :=
  .seq (.block powP48) (.seq (batch 4 fun _ => []) (.seq (batch 8 fun _ => [])
    (.seq (.loop body48 .ae) (.block (.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv))))))

def bigDP : Prog isa :=
  .seq (.block powP48) (.seq (.loop dbody48 .ae) (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)]))

def enc : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 256)])
        (.seq (.ite .b (.block []) bigP)
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop body .ae))
              (.block (storeCtr ++ lastG ++ storeY)))))))

def dec : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq (.block [.alu .cmp .r9 (.imm 256)])
      (.seq (.ite .b (.block []) bigDP)
        (.seq (.block [.alu .cmp .r9 (.imm 16)])
          (.seq (.ite .b (.block []) (.loop dbody .ae))
            (.block (storeCtr ++ storeY))))))

end VG.Impl.Gcm.X86_64.StitchZH
