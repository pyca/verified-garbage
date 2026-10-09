import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH

/-! # Out-of-place GCM with prepared powers and cached AES keys -/

namespace VG.Impl.Gcm.X86_64.StitchZHTo
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ)
open VG.Impl.Gcm.X86_64.StitchZ (gq gq48 lastG adv)
open VG.Impl.Gcm.X86_64.StitchZTo (xorDataZTo)
open VG.Impl.Gcm.X86_64.StitchZR (powP48)
open VG.Impl.Gcm.X86_64.StitchZRTo (setupP)

def batchTo (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsZ .xmm14 .xmm0 .xmm15 aregs)) (.seq (Aes.X86_64.VaesZH.aes aregs g) (.block (xorDataZTo .xmm13 .rdx .r8 aregs j)))

def firstTo : Prog isa := batchTo 0 fun _ => []

def bodyTo : Prog isa :=
  .seq (batchTo 4 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])

def body48To : Prog isa :=
  .seq (batchTo 12 (gq48 0)) (.seq (batchTo 16 (gq48 1)) (.seq (batchTo 20 (gq48 2))
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 96)])))

def bigRestTo : Prog isa :=
  .seq (batchTo 4 fun _ => []) (.seq (batchTo 8 fun _ => [])
    (.seq (.loop body48To .ae) (.block (.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv)))))

def bigPTo : Prog isa := .seq (.block powP48) bigRestTo

def encWith (su : List Instr) (bigC : Prog isa) : Prog isa :=
  .seq (.seq (.block su) Aes.X86_64.VaesZH.loadKeys)
    (.seq firstTo
      (.seq (.block [.alu .cmp .r9 (.imm 256)])
        (.seq (.ite .b (.block []) bigC)
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop bodyTo .ae))
              (.block (storeCtr ++ lastG ++ storeY)))))))

def encP : Prog isa := encWith setupP bigPTo

/-- The blocks after the last group, as `StitchZH.rem`'s, read at
`rdx + r8` (`r8` is `src - dst`). -/
def remTo : Prog isa := StitchZH.remWith [.alu .add .r8 (.reg .rdx)] .r8

/-- `encP`, for any number of blocks from 16 on. -/
def encR : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq firstTo
      (.seq (.block [.alu .cmp .r9 (.imm 256)])
        (.seq (.ite .b (.block []) bigPTo)
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop bodyTo .ae)) (StitchZH.tailR remTo))))))

end VG.Impl.Gcm.X86_64.StitchZHTo
