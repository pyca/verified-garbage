module
public import VerifiedGarbage.TCB.AArch64.Isa

/-! ROMix moves complete 128-byte blocks. Four vector words per iteration
halve address updates relative to a 16-byte loop while using caller-saved
vectors only. The counters retain their original units of eight bytes. -/
@[expose] public section
namespace VG.Impl.Scrypt.AArch64.Transfer
open VG VG.AArch64

def vr (k : Nat) : VReg := #[.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7].getD k .v0

def loads (b : Reg) (v : Nat) : List Instr :=
  (List.range 4).map fun j => .ldrq (vr (v+j)) b (16*j)

def stores (b : Reg) : List Instr :=
  (List.range 4).map fun j => .strq (vr j) b (16*j)

def xors : List Instr :=
  (List.range 4).map fun j => .vop (.logic .eor (vr j) (vr j) (vr (4+j)))

def copyPacket : List Instr := loads .x9 0 ++ stores .x10

def xorPacket : List Instr := loads .x9 0 ++ loads .x10 4 ++ xors ++ stores .x11

def copyLoop : Prog isa := .loop (.block (copyPacket ++
  [.addImm .x .x9 .x9 64,.addImm .x .x10 .x10 64,.subImm .x .x11 .x11 8])) (.nonzero .x .x11)

def xorLoop : Prog isa := .loop (.block (xorPacket ++
  [.addImm .x .x9 .x9 64,.addImm .x .x10 .x10 64,.addImm .x .x11 .x11 64,
    .subImm .x .x12 .x12 8])) (.nonzero .x .x12)
end VG.Impl.Scrypt.AArch64.Transfer
