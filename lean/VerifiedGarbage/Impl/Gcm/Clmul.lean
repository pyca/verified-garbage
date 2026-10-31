module

/-! # Constants for reflected carryless GHASH -/

@[expose] public section
namespace VG.Impl.Gcm.Clmul

def poly : BitVec 64 := 0xc200000000000000#64

def xInv2Hi : BitVec 64 := 0x4600000000000000#64

end VG.Impl.Gcm.Clmul
