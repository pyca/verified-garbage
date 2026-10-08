import VerifiedGarbage.Impl.P256.Linear
import VerifiedGarbage.Impl.P256.VerifySparse
import VerifiedGarbage.Impl.P256.EcdhAllocatedCode

/-! Five-square, three-multiply Jacobian doubling with fused linear reductions.
The scheduler is untrusted; its output is certified against the raw arithmetic. -/
namespace VG.Impl.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
def raw : List Instr :=
  let z2:=800; let y2:=832; let t1:=864; let t2:=896; let xy2:=928; let d:=960
  let f := VerifySparse.op
  f (.mul z2 576 576)++f (.mul y2 544 544)++
  f (.sub t2 512 z2)++Linear.weakAdd t1 512 z2++
  f (.mul t2 t1 t2)++f (.add t1 544 576)++
  f (.mul xy2 512 y2)++f (.mul d t2 t2)++f (.mul t1 t1 t1)++
  Linear.linear129 d xy2 d++f (.sub t1 t1 z2)++
  f (.sub 576 t1 y2)++Linear.linear41 512 xy2 d++
  f (.mul t2 d t2)++f (.mul z2 y2 y2)++Linear.linear38 544 t2 z2

def keep (off : Nat) : Bool := 512≤off && off<608

def code : List Instr := EcdhAllocatedCode.double

def program : Prog isa := .block code

end VG.Impl.P256.EcdhDouble
