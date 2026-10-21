module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH

/-! # Out-of-place GCM with prepared powers and cached AES keys -/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchZHTo
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeY)
open VG.Impl.Gcm.X86_64.Slot (ctrsM storeCtr)
open VG.Impl.Gcm.X86_64.StitchZ (gq gq48 lastG adv bigMinPE)
open VG.Impl.Gcm.X86_64.StitchZTo (xorDataZTo)
open VG.Impl.Gcm.X86_64.StitchZR (powP48)
open VG.Impl.Gcm.X86_64.StitchZRTo (setupP)

def batchTo (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsM aregs)) (.seq (Aes.X86_64.VaesZH.aes aregs g) (.block (xorDataZTo .xmm13 .rdx .r8 aregs j)))

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
def remTo : Prog isa := StitchZH.remG [.alu .add .r8 (.reg .rdx)] .r8

/-- `encP`, for any number of blocks from 16 on. -/
def encR : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq firstTo
      (.seq (.block [.alu .cmp .r9 (.imm bigMinPE)])
        (.seq (.ite .b (.block []) bigPTo)
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop bodyTo .ae)) (StitchZH.tailR remTo))))))

/-! ## In one pass over a source and then in place

`encN` is `encR`'s loops over the `r9` whole groups at `src`, `r8 = src -
dst` (`phase1`), and then, with `r9` increased by `rbp`, `StitchZH`'s loop
over the groups at `dst` after them, in place: both keep the AES keys in
registers, write at `rdx` and count down `r9`, so the in-place loop goes on
from the group the out-of-place one encrypted last. `r8` is set to `dst`
(`rbx`) as the in-place loop's data pointer. -/

/-- The out-of-place loops over the whole groups at `src`, up to the last
group's hash. -/
def phase1 : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq firstTo
      (.seq (.block [.alu .cmp .r9 (.imm bigMinPE)])
        (.seq (.ite .b (.block []) bigPTo)
          (.seq (.block [.alu .cmp .r9 (.imm 32)]) (.ite .b (.block []) (.loop bodyTo .ae))))))

/-- `phase1`, then the `rbp` blocks at `dst` after `src`'s, in place. -/
def encN : Prog isa :=
  .seq phase1
    (.seq (.block [.mov .r8 (.reg .rbx), .alu .add .r9 (.reg .rbp), .alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop StitchZH.body .ae)) (.block (storeCtr ++ lastG ++ storeY))))

end VG.Impl.Gcm.X86_64.StitchZHTo
