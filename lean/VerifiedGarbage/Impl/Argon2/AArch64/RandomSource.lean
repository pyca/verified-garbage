module

public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
public import VerifiedGarbage.Impl.Argon2.AArch64.AddressMode
public import VerifiedGarbage.Impl.Argon2.AArch64.AddressCache
public import VerifiedGarbage.Impl.Argon2.AArch64.DependentWord

/-! Dispatch the filling random word using the public segment addressing mode. -/

@[expose] public section

namespace VG.Impl.Argon2.AArch64.RandomSource

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def test : List Instr := [comparei .x6 0].flatten

def prepare : Prog isa := .seq AddressMode.code (.block test)

def code : Prog isa := .seq prepare (.ite (.zero .x .x15) DependentWord.code AddressCache.code)

end VG.Impl.Argon2.AArch64.RandomSource
