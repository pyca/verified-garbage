module

public import VerifiedGarbage.Impl.Dsa.X86_64.Random

/-! # Randomized signing wrapper on x86-64

The signer is a parameter, so registration can propagate every arithmetic
backend. This program is not yet registered: its complete Verified proof is
required before emitting assembly or replacing the Rust retry loop.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.RandomSign
open VG VG.X86_64 Random

/-- Incoming stack argument j, after allocating the frame. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

def copyArg (j slot : Nat) : List Instr :=
  [.mov .rax (.mem (arg j)), .store (sp slot) .rax]

/-- Preserve all arguments across calls and start with no consumed bytes. -/
def entry : List Instr :=
  [.store (sp oOut) .rdi, .store (sp oOutLen) .rsi, .store (sp oUsedPtr) .rdx,
   .store (sp oKey) .rcx, .store (sp oKeyLen) .r8, .store (sp oPLen) .r9,
   .alu .add .rcx (.reg .r9), .store (sp oQ) .rcx,
   .mov .rax (.imm 0), .store (sp oUsed) .rax,
   .mov .rax (.imm 8), .store (sp oAttempts) .rax] ++
  copyArg 0 oQLen ++ copyArg 1 oDigest ++ copyArg 2 oDigestLen ++
  copyArg 3 oRand ++ copyArg 4 oRandLen ++ copyArg 5 oScratch ++ copyArg 6 oScratchLen

/-- Supplied-nonce signing's six register and five stack arguments. -/
def callArgs : List Instr :=
  [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOutLen)),
   .mov .rdx (.mem (sp oKey)), .mov .rcx (.mem (sp oKeyLen)),
   .mov .r8 (.mem (sp oPLen))] ++ address .r9 oNonce ++
  [ .mov .rax (.mem (sp oQLen)), .store (sp 0) .rax,
    .mov .rax (.mem (sp oDigest)), .store (sp 8) .rax,
    .mov .rax (.mem (sp oDigestLen)), .store (sp 16) .rax,
    .mov .rax (.mem (sp oScratch)), .store (sp 24) .rax,
    .mov .rax (.mem (sp oScratchLen)), .store (sp 32) .rax ]

/-- One signing attempt. Status 4 means a further attempt is needed. -/
def attempt (name : String) (signer : Prog isa) : Prog isa :=
  .seq sample
    (.seq (.block [.alu .cmp .rax (.imm 1)])
      (.ite .e
        (.seq (.block callArgs)
          (.seq (.call name signer)
            (.seq (.block [.store (sp oStatus) .rax, .alu .cmp .rax (.imm 0)])
              (.ite .e
                (.seq (.block [.mov .rax (.mem (sp oAttempts)), .alu .sub .rax (.imm 1),
                    .store (sp oAttempts) .rax])
                  (.ite .ne (.block [.mov .rax (.imm 4), .store (sp oStatus) .rax]) (.block [])))
                (.block [])))))
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
