module

public import VerifiedGarbage.Impl.Dsa.X86.KeyRandom

/-! # Bounded DSA key generation on i686

Check p||q||g before consuming any tape, sample x from [1,q), then
derive p||q||g||y||x. The two calls are parameters of the wrapper.
Every exit clears the scalar; failures clear the entire output.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.GenerateKey
open VG VG.X86 VG.Impl.Mont.X86 KeyRandom

def entry : List Instr :=
  [.store (sp oSaveEbx) .ebx, .store (sp oSaveEsi) .esi,
    .store (sp oSaveEdi) .edi, .store (sp oSaveEbp) .ebp,
    .mov .eax (.imm 0), .store (sp oUsed) .eax, .store (sp oStatus) .eax]

def copyArg (j i : Nat) : List Instr :=
  [.mov .eax (.mem (arg j)), .store (sp (4 * i)) .eax]

def checkArgs : List Instr :=
  copyArg aKey 0 ++ copyArg aKeyLen 1 ++ copyArg aPLen 2 ++
  copyArg aQLen 3 ++ copyArg aScratch 4 ++ copyArg aScratchLen 5

def deriveArgs : List Instr :=
  copyArg aOut 0 ++ copyArg aOutLen 1 ++ copyArg aKey 2 ++ copyArg aKeyLen 3 ++
  copyArg aPLen 4 ++
  [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 oNonce)),
    .store (sp 20) .eax] ++
  copyArg aQLen 6 ++ copyArg aScratch 7 ++ copyArg aScratchLen 8

def sampledWith (derive : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .eax (.imm 1)])
    (.ite .e
      (.seq (.block deriveArgs)
        (.seq derive (.block [.store (sp oStatus) .eax])))
      (.block []))

def sampled (derive : String) (deriveKey : Prog isa) : Prog isa :=
  sampledWith (.call derive deriveKey)

def generateWith (derive : Prog isa) : Prog isa :=
  .seq prepare
    (.seq (.block [.alu .cmp .eax (.imm 0)])
      (.ite .e (.block [.store (sp oStatus) .eax])
        (.seq sample (sampledWith derive))))

def generate (derive : String) (deriveKey : Prog isa) : Prog isa :=
  generateWith (.call derive deriveKey)

def zeroOut : Prog isa :=
  .seq (.block [.mov .esi (.mem (arg aOut)), .mov .ecx (.mem (arg aOutLen)), .mov .eax (.imm 0)])
    (.loop (.block [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]) .ne)

/-- Zero the output on failure, clear the nonce, publish the consumption
(a 64-bit count), and restore the callee-saved registers. -/
def finish : Prog isa :=
  .seq (.block [.mov .eax (.mem (sp oStatus)), .alu .cmp .eax (.imm 1)])
    (.seq (.ite .ne zeroOut (.block []))
      (.block (clearNonce ++ [.mov .edx (.mem (arg aUsed)), .mov .eax (.mem (sp oUsed)),
        .store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax,
        .mov .ebx (.mem (sp oSaveEbx)), .mov .esi (.mem (sp oSaveEsi)),
        .mov .edi (.mem (sp oSaveEdi)), .mov .ebp (.mem (sp oSaveEbp)),
        .mov .eax (.mem (sp oStatus))])))

def bodyWith (check derive : Prog isa) : Prog isa :=
  .seq (.block (entry ++ checkArgs))
    (.seq check
      (.seq (.block [.alu .cmp .eax (.imm 0)])
        (.seq (.ite .e (.block []) (generateWith derive)) finish)))

def body (check derive : String) (checkParameters deriveKey : Prog isa) : Prog isa :=
  bodyWith (.call check checkParameters) (.call derive deriveKey)

def codeWith (check derive : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (bodyWith check derive) (.free frameBytes)

def code (check derive : String) (checkParameters deriveKey : Prog isa) : Prog isa :=
  codeWith (.call check checkParameters) (.call derive deriveKey)

end VG.Impl.Dsa.X86.GenerateKey
