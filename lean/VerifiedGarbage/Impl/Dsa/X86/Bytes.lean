module

public import VerifiedGarbage.Impl.Weierstrass.X86

/-! # DSA's fixed-width big-endian components on 32-bit x86

The byte routines shared with elliptic-curve code also handle the padded
DSA scalar widths. They access only the requested input/output bytes.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86

def loadComponent (len n out : Nat) : List Instr :=
  VG.Impl.Weierstrass.X86.loadBytes len n out .esi

def storeComponent (len n input : Nat) : List Instr :=
  VG.Impl.Weierstrass.X86.storeBytes len n .esi 0 input

end VG.Impl.Dsa.X86
