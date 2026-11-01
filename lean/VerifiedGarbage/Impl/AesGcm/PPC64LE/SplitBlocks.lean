module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks

/-! # Source-prefix readers for the shared POWER8 GCM batch -/

@[expose] public section

namespace VG.Impl.AesGcm.PPC64LE.SplitBlocks
open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Blocks

-- r17 points to the unconsumed external prefix; r19 counts its blocks.
-- Only the batch crossing its end needs a choice for each vector load.
def partialLoad (i : Nat) : Prog isa :=
 .seq (.block [.subi .r12 .r19 (i+1),.lsr .d .r12 .r12 63])
 (.ite (.zero .d .r12) (.block [.lxvd2x (dataReg i) .r17 (dataOffset i)])
   (.block [.lxvd2x (dataReg i) .r6 (dataOffset i)]))

def partialLoadsFrom : Nat → Nat → Prog isa
 | _,0 => .block []
 | start,count+1 => .seq (partialLoad start) (partialLoadsFrom (start+1) count)

def load : Prog isa :=
 .ite (.zero .d .r19) (.block dataLoad)
 (.seq (.block [.lsr .d .r12 .r19 3])
 (.ite (.nonzero .d .r12)
   (.block (dataLoadAt .r17 ++ [.addi .r17 .r17 128,.subi .r19 .r19 8]))
   (.seq (partialLoadsFrom 0 8)
     (.block [.lsl .r12 .r19 4,.add .r17 .r17 .r12,.li .r19 0]))))

def batch : Prog isa := batchWith
 (.seq load (.block (storesFinish ++ ghStart ++ ghCode)))

def code : Prog isa := codeWith batch

end VG.Impl.AesGcm.PPC64LE.SplitBlocks
