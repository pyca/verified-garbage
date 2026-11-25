module
public meta import VerifiedGarbage.Impl.P256.VerifyArithmetic
public meta import VerifiedGarbage.Impl.P256.VerifySparse
public meta import VerifiedGarbage.Impl.P256.Linear
public meta import VerifiedGarbage.Impl.P256.EcdhJac.Base
public meta import Init.System.IO
open VG.AArch64 VG.Impl.P256 VG.Impl.Weierstrass
public meta section
deriving instance Repr for Instr
def dbl : List Instr :=
  let z2:=800; let y2:=832; let t1:=864; let t2:=896; let xy2:=928; let d:=960
  let f := VerifySparse.op
  f (.mul z2 576 576)++f (.mul y2 544 544)++
  f (.sub t2 512 z2)++Linear.weakAdd t1 512 z2++
  f (.mul t2 t1 t2)++f (.add t1 544 576)++
  f (.mul xy2 512 y2)++f (.mul d t2 t2)++f (.mul t1 t1 t1)++
  Linear.linear129 d xy2 d++f (.sub t1 t1 z2)++
  f (.sub 576 t1 y2)++Linear.linear41 512 xy2 d++
  f (.mul t2 d t2)++f (.mul z2 y2 y2)++Linear.linear38 544 t2 z2
def raw (k : VerifyArithmetic.Kind) : List Instr := (VerifyArithmetic.operations k).flatMap VerifySparse.op
run_cmd do
  let out (n : String) (l : List Instr) : IO Unit :=
    IO.FS.writeFile ("/tmp/sp/" ++ n ++ ".raw") ("\n".intercalate (l.map fun i => (toString (repr i)).replace "\n" " "))
  out "double" dbl
  out "mixedHead" (raw .mixedHead)
  out "mixedTail" (raw .mixedTail)
  out "jacTail" (raw .jacTail)
  out "cachedHead" (raw .cachedHead)
  out "dblu" (EcdhJac.dbluOps.flatMap VerifySparse.op)
  out "zaddu" (EcdhJac.zadduOps.flatMap VerifySparse.op)
end
