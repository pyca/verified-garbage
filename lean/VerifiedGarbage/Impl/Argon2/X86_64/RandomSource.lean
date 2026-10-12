module

public import VerifiedGarbage.Impl.Argon2.X86_64.AddressMode
public import VerifiedGarbage.Impl.Argon2.X86_64.AddressCache
public import VerifiedGarbage.Impl.Argon2.X86_64.DependentWord

/-! Dispatch the filling random word using the public segment addressing mode. -/

@[expose] public section

namespace VG.Impl.Argon2.X86_64.RandomSource

variable [Compressor]

open VG.X86_64

def test : List Instr := [.alu .cmp .r10 (.imm 0)]

def prepare : Prog isa := .seq AddressMode.code (.block test)

def code : Prog isa := .seq prepare (.ite .e DependentWord.code AddressCache.code)

end VG.Impl.Argon2.X86_64.RandomSource
