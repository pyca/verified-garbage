module

public import VerifiedGarbage.Impl.Dsa.X86_64.Random

/-! # Randomized signing wrapper on x86-64

The signer is a parameter, so registration can propagate every arithmetic
backend. The complete verification covers rejection sampling, bounded signing
retries, output clearing and the declared leakage trace.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.RandomSign
open VG VG.X86_64 Random

/-- Incoming stack argument j, after allocating the frame. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

def copyArg (j slot : Nat) : List Instr :=
  copySlot (frameBytes + 8 + 8 * j) slot

/-- Preserve all arguments across calls and start with no consumed bytes. -/
def entryHeader : List Instr :=
  [.store (sp oOut) .rdi, .store (sp oOutLen) .rsi, .store (sp oUsedPtr) .rdx,
   .store (sp oKey) .rcx, .store (sp oKeyLen) .r8, .store (sp oPLen) .r9,
   .alu .add .rcx (.reg .r9), .store (sp oQ) .rcx,
   .mov .rax (.imm 0), .store (sp oUsed) .rax,
   .mov .rax (.imm 8), .store (sp oAttempts) .rax]

def incomingSlots : List (Nat × Nat) :=
  [(256, oQLen), (264, oDigest), (272, oDigestLen), (280, oRand),
    (288, oRandLen), (296, oScratch), (304, oScratchLen)]

def entry : List Instr :=
  entryHeader ++ incomingSlots.flatMap (fun p => copySlot p.1 p.2)

/-- Supplied-nonce signing's six register and five stack arguments. -/
def callArgs : List Instr :=
  [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOutLen)),
   .mov .rdx (.mem (sp oKey)), .mov .rcx (.mem (sp oKeyLen)),
   .mov .r8 (.mem (sp oPLen))] ++ address .r9 oNonce ++
  [(oQLen, 0), (oDigest, 8), (oDigestLen, 16), (oScratch, 24), (oScratchLen, 32)].flatMap
    (fun p => copySlot p.1 p.2)

/-- Save the supplied-nonce signer's result and advance the retry counter. -/
def callFinish : Prog isa :=
  .seq (.block [.mov32 .rax (.reg .rax), .store (sp oStatus) .rax, .alu .cmp .rax (.imm 0)])
    (.ite .e
      (.seq (.block [.mov .rax (.mem (sp oAttempts)), .alu .sub .rax (.imm 1),
          .store (sp oAttempts) .rax])
        (.ite .ne (.block [.mov .rax (.imm 4), .store (sp oStatus) .rax]) (.block [])))
      (.block []))

/-- One signing attempt. Status 4 means a further attempt is needed. -/
def attempt (name : String) (signer : Prog isa) : Prog isa :=
  .seq sample
    (.seq (.block [.alu .cmp .rax (.imm 1)])
      (.ite .e
        (.seq (.block callArgs) (.seq (.call name signer) callFinish))
        (.block [])))

/-- All failures zero the full signature, including failure before any call. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .r10 (.mem (sp oOut)), .mov .r11 (.mem (sp oOutLen)),
      .mov .rax (.imm 0)])
    (.loop (.block [.store8 { base := .r10 } .rax, .alu .add .r10 (.imm 1),
      .alu .sub .r11 (.imm 1)]) .ne)

/-- Publish complete-draw consumption and wipe the nonce on every exit. -/
def finish : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp oStatus)), .alu .cmp .rax (.imm 1)])
    (.seq (.ite .ne zeroOut (.block []))
      (.block (clearNonce ++ [.mov .rdx (.mem (sp oUsedPtr)), .mov .rax (.mem (sp oUsed)),
        .store { base := .rdx } .rax, .mov .rax (.mem (sp oStatus))])))

def body (name : String) (signer : Prog isa) : Prog isa :=
  .seq (.block entry)
    (.seq prepare
      (.seq (.block [.alu .cmp .rax (.imm 0)])
        (.seq (.ite .e (.block [.store (sp oStatus) .rax])
          (.loop (.seq (attempt name signer) (.block [.mov .rax (.mem (sp oStatus)),
            .alu .cmp .rax (.imm 4)])) .e)) finish)))

/-- The frame preserves stack alignment and all loop state across the call. -/
def code (name : String) (signer : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body name signer) (.free frameBytes)

end VG.Impl.Dsa.X86_64.RandomSign
