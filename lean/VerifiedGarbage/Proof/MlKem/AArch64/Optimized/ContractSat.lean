module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ConstsSat
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64

def addTables (s : State) : State :=
 {s with mem:=tableMem,syms:=tableSyms,rd:=s.rd++Abi.constRegions tableSyms constants}

theorem strip_addTables (s : State) : stripConsts constants (addTables s) =
 {s with mem:=tableMem,syms:=tableSyms} := by
 have hl : (Abi.constRegions tableSyms constants).length=constants.length := by
  simp only [Abi.constRegions,List.length_map]
 simp only [stripConsts,addTables,State.withRegions,List.length_append,hl,Nat.add_sub_cancel,List.take_left]

end VG.Proof.MlKem.AArch64.Optimized
