module

public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign

/-! # DSA key generation on x86-64

`vg_dsa_generate_key` checks the domain with `vg_dsa_check_parameters`,
samples x as the randomized signer samples its nonce, and derives the key
with `vg_dsa_derive_key`. Both callees are parameters, so registration can
propagate every arithmetic backend. The frame is the randomized signer's:
the packed domain takes the key's slots, and the sampled x the nonce's.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.GenerateKey
open VG VG.X86_64 Random

/-- Preserve all arguments across calls and start with no consumed bytes. -/
def entryHeader : List Instr :=
  [.store (sp oOut) .rdi, .store (sp oOutLen) .rsi, .store (sp oUsedPtr) .rdx,
   .store (sp oKey) .rcx, .store (sp oKeyLen) .r8, .store (sp oPLen) .r9,
   .alu .add .rcx (.reg .r9), .store (sp oQ) .rcx,
   .mov .rax (.imm 0), .store (sp oUsed) .rax, .store (sp oStatus) .rax]

/-- q_len, rand, rand_len, scratch and scratch_len, past the return address. -/
def incomingSlots : List (Nat × Nat) :=
  [(256, oQLen), (264, oRand), (272, oRandLen), (280, oScratch), (288, oScratchLen)]

def entry : List Instr :=
  entryHeader ++ incomingSlots.flatMap (fun p => copySlot p.1 p.2)

/-- The domain check's six register arguments. -/
def checkArgs : List Instr :=
  [.mov .rdi (.mem (sp oKey)), .mov .rsi (.mem (sp oKeyLen)), .mov .rdx (.mem (sp oPLen)),
   .mov .rcx (.mem (sp oQLen)), .mov .r8 (.mem (sp oScratch)), .mov .r9 (.mem (sp oScratchLen))]

/-- Derivation's six register and three stack arguments; x is the sampled
scalar in the nonce's slot. -/
def deriveArgs : List Instr :=
  [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOutLen)),
   .mov .rdx (.mem (sp oKey)), .mov .rcx (.mem (sp oKeyLen)),
   .mov .r8 (.mem (sp oPLen))] ++ address .r9 oNonce ++
  [(oQLen, 0), (oScratch, 8), (oScratchLen, 16)].flatMap (fun p => copySlot p.1 p.2)

/-- Keep a callee's 32-bit result as the status. -/
def keepStatus : List Instr :=
  [.mov32 .rax (.reg .rax), .store (sp oStatus) .rax]

/-- Sample x and, once accepted, derive the key from it. -/
def generate (derive : String) (deriveKey : Prog isa) : Prog isa :=
  .seq prepare
    (.seq (.block [.alu .cmp .rax (.imm 0)])
      (.ite .e (.block [.store (sp oStatus) .rax])
        (.seq sample
          (.seq (.block [.store (sp oStatus) .rax, .alu .cmp .rax (.imm 1)])
            (.ite .e (.seq (.block deriveArgs) (.seq (.call derive deriveKey) (.block keepStatus)))
              (.block []))))))

def body (check derive : String) (checkParameters deriveKey : Prog isa) : Prog isa :=
  .seq (.block (entry ++ checkArgs))
    (.seq (.call check checkParameters)
      (.seq (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 0)])
        (.seq (.ite .e (.block []) (generate derive deriveKey)) RandomSign.finish)))

/-- The frame preserves stack alignment and all state across the calls. -/
def code (check derive : String) (checkParameters deriveKey : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body check derive checkParameters deriveKey) (.free frameBytes)

end VG.Impl.Dsa.X86_64.GenerateKey
