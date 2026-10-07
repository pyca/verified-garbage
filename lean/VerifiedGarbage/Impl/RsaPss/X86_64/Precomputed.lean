import VerifiedGarbage.Impl.RsaPss.X86_64

namespace VG.Impl.RsaPss.X86_64.Precomputed

open VG VG.X86_64

/-- The public operation's arguments, using the caller's cached modulus. -/
def pubArgs : List Instr := X86_64.pubArgs ++
  [.mov .rdx (.mem (arg 5)), .mov .rcx (.mem (arg 6))]

variable (H : Pbkdf2.Md.X86_64.Hash) (pubN : String) (pubC : Prog isa)

def main : Prog isa :=
  seqs [.block dbSlots, .block pubArgs, .call pubN pubC, .block acc0, mgfXor H, .block clearTop,
    posScan, posCheck H, clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H]

def body : Prog isa :=
  seqs [.block (verifyPrologue ++ n0),
    .ite .e verifyFail (seqs [.block smear, emLen H,
      .ite .b verifyFail (seqs [anyArgs, .block ([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)),
          .alu .sub .rax (.reg .r8)] ++ saltFits H),
        .ite .b verifyFail (main H pubN pubC)])]),
    .block restoreRegs]

def code : Prog isa := .frame (.alloc frameBytes) (body H pubN pubC) (.free frameBytes)

end VG.Impl.RsaPss.X86_64.Precomputed
