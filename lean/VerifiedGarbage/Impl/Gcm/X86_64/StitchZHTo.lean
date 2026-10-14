module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH

/-! # Out-of-place GCM with prepared powers and cached AES keys -/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchZHTo
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ)
open VG.Impl.Gcm.X86_64.StitchZ (gq gq48 lastG adv)
open VG.Impl.Gcm.X86_64.StitchZTo (xorDataZTo)
open VG.Impl.Gcm.X86_64.StitchZR (powP48)
open VG.Impl.Gcm.X86_64.StitchZRTo (setupP)

def batchTo (j : Nat) (g : Nat → List Instr) (be : Bool := false) : Prog isa :=
  .seq (StitchZH.ctrs be) (.seq (Aes.X86_64.VaesZH.aes aregs g) (.block (xorDataZTo .xmm13 .rdx .r8 aregs j)))

/-- The first group, encrypted only; with a public block index (`be`), after
`StitchZH.beSetup`, the index being at `[rsp + 32]`. -/
def firstTo (be : Bool := false) : Prog isa :=
  if be then .seq (.block (StitchZH.beSetup 32)) (batchTo 0 (fun _ => []) true) else batchTo 0 fun _ => []

def bodyTo (be : Bool := false) : Prog isa :=
  .seq (batchTo 4 gq be) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])

def body48To (be : Bool := false) : Prog isa :=
  .seq (batchTo 12 (gq48 0) be) (.seq (batchTo 16 (gq48 1) be) (.seq (batchTo 20 (gq48 2) be)
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 96)])))

def bigRestTo (be : Bool := false) : Prog isa :=
  .seq (batchTo 4 (fun _ => []) be) (.seq (batchTo 8 (fun _ => []) be)
    (.seq (.loop (body48To be) .ae) (.block (.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv)))))

def bigPTo (be : Bool := false) : Prog isa := .seq (.block powP48) (bigRestTo be)

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
def remTo : Prog isa := StitchZH.remG [.alu .add .r8 (.reg .rdx)] .r8

/-- `encP`, for any number of blocks from 16 on. -/
def encR (be : Bool := false) : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq (firstTo be)
      (.seq (.block [.alu .cmp .r9 (.imm 256)])
        (.seq (.ite .b (.block []) (bigPTo be))
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop (bodyTo be) .ae)) (StitchZH.tailR remTo))))))

end VG.Impl.Gcm.X86_64.StitchZHTo
