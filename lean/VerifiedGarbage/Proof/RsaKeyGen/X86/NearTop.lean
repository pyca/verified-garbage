module

public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The native words the separation comparison reads -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def word (m : Mem) (base : Addr) (offset : Nat) : BitVec 32 := m.readW (off base offset) 32

end VG.Proof.RsaKeyGen.X86.Near
