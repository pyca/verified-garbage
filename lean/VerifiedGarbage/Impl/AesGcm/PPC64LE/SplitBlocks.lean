module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks

/-! # Source-prefix readers for the shared POWER8 GCM batch -/

@[expose] public section

namespace VG.Impl.AesGcm.PPC64LE.SplitBlocks
open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Blocks
open VG.Impl.Aes.PPC64LE.Crypto (mov)

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

def batch : Prog isa := batchWithStore (.seq load (.block storesFinish))

def code : Prog isa := codeWith batch

-- The kernel leaves these registers available to track the external prefix.
-- Their caller values fit between the core's spills and its tables.
def extraSaved : List (Reg × Nat) := [(.r17,152),(.r19,160)]

def argsHead : List Instr := [.addSp .r12 0,.load .d .r11 .r12 96]

def argsConfig : List Instr :=
 [mov .r17 .r7,mov .r19 .r8,mov .r7 .r9,mov .r8 .r10,mov .r9 .r11]

def argsRest : List Instr := extraSaved.map (fun (r,o) => .store .d r .r11 o) ++ argsConfig

def bulk : Prog isa := .seq (.block bulkArgs) (.seq code (.block bulkRest))

-- Only short inputs, or at most seven blocks after the bulk loop, need
-- their external prefix copied before the existing CTR/GHASH tail.
def copyStep : List Instr := [.lxvd2x U .r17 .r0,.stxvd2x U .r11 .r0,
 .addi .r17 .r17 16,.addi .r11 .r11 16,.subi .r19 .r19 1]

def copyPrefix : Prog isa := .ite (.zero .d .r19) (.block [])
 (.seq (.block [mov .r11 .r30,.li .r0 0])
 (.loop (.block copyStep) (.nonzero .d .r19)))

def restoreExtra : List Instr := extraSaved.map (fun (r,o) => .load .d r .r31 o)

def maybeBulk : Prog isa := .ite (.zero .d .r12) (.block []) bulk

def body : Prog isa := .seq (.block wrapperEntry) (.seq maybeBulk
 (.seq copyPrefix (.seq (.block restoreExtra) (.seq tail (.block wrapperExit)))))

def head : Prog isa := .block argsHead

def rest : Prog isa := .seq (.block argsRest) body

/-- Nine-argument whole-block helper; `scratch` is at the incoming `sp+96`.
Restore the extra saves before the leaf calls reuse the core's scratch. -/
def encrypt : Prog isa := .ite (.zero .d .r10) (.block [])
 (.seq head rest)

end VG.Impl.AesGcm.PPC64LE.SplitBlocks
